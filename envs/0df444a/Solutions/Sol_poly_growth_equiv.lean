-- Prove2me | solution 1 for poly_growth_equiv
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T23:20:30.031337+00:00
-- url     : https://prove2.me/submissions/3339cc54-dae5-4252-a2a7-df3df620af01

import Mathlib

section
-- module Solutions.OAIQ093_PR.Unitary_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Subgroups of the unitary group

Properness and compactness of the unitary group, the transfer of polynomial growth along a
group isomorphism, and the distance estimate `small_dist_matrix`.
-/


open scoped Matrix.Norms.L2Operator ComplexInnerProductSpace

set_option linter.style.longLine false
set_option linter.style.commandStart false

open Subgroup Pointwise Finset
open scoped Pointwise Finset
open scoped commutatorElement IsMulCommutative


-- Like 'mem_closure_prod_list', but without requring that the generating set be symmetric
lemma weak_mem_closure_prod_list {G: Type*} [Group G] (S: Set G) (x: G) (hx: x ∈ Subgroup.closure S): ∃ l: List (↑(S ∪ S⁻¹)), l.unattach.prod = x := by
  -- https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/Group.20.28.2FMonoid.2Fetc.29.20closures.20are.20a.20finite.20product.2Fsum/near/477951441
  have foo := Submonoid.exists_list_of_mem_closure (s := S ∪ S⁻¹) (x := x)
  rw [← Subgroup.closure_toSubmonoid _] at foo
  specialize foo hx
  obtain ⟨l, ⟨mem_s, prod_eq⟩⟩ := foo
  use (l.attach).map (fun x => ⟨x.val, mem_s (x.val) x.property⟩)
  unfold List.unattach
  simp [prod_eq]


-- Proof of proposition 2.18
-- Note - we additionaly assume that the generating set contains 1, as this us use a simpler
-- definition of polynomial growth (since S^n ⊆ S^(n+1))
-- We use this requirement throughout the entire proof, so it's fine
-- At the very start of the proof, we'll use a more general definition of polynomial growth
-- (using the word metric) to drop the assumptions on our generating set,
-- and then reduce the proof to the case of a symmetric generating set containing 1
lemma poly_growth_equiv_oai {G: Type*} [DecidableEq G] [Group G] (a d: ℕ)
  (a_pos: 0 < a)
  (S S': Finset G)
  (S_symm: S = S⁻¹)
  (S_one: 1 ∈ S)
  (S_generates: Subgroup.closure (S : Set G) = ⊤)
  (s_poly: ∀ n ≥ 1, #(S ^ n) ≤ a * n ^ d):
  ∃ b: ℕ, 1 ≤ b ∧ ∀ n ≥ 1, #(S' ^ n) ≤ b * n^d := by


  by_cases g_nontrivial: Nontrivial G
  .
    let S'_prod := fun (s: S') => (weak_mem_closure_prod_list S s.val (by
      simp [S_generates]
    )).choose

    let all_lists := (Finset.image S'_prod Finset.univ)
    let max_len := all_lists.sup (fun l => l.length)
    by_cases max_len_zero: max_len = 0
    .
      unfold max_len at max_len_zero
      simp at max_len_zero
      simp [all_lists] at max_len_zero


      have S'_one: S' ⊆ {1} := by
        intro s' hs'
        have bad_prod := max_len_zero (S'_prod ⟨s', hs'⟩) s' hs' rfl
        simp [S'_prod] at bad_prod
        have s'_prod := (weak_mem_closure_prod_list S s' (by
          simp [S_generates]
        )).choose_spec
        rw [bad_prod] at s'_prod
        simp at s'_prod
        rw [← s'_prod]
        simp

      have S'_le: #(S') ≤ 1 := by
        grw [Finset.card_le_card (t := {1})]
        simp
        apply S'_one


      use 1
      refine ⟨by simp, ?_⟩
      intro n hn
      simp
      grw [Finset.card_pow_le]
      grw [S'_le]
      simp
      exact Nat.one_le_pow d n hn

    .
      have start_pos_nonzero: 1 ≤ max_len := by omega
      use a * (max_len ^ d)
      refine ⟨?_, ?_⟩
      .
        rw [Nat.one_le_iff_ne_zero]
        apply Nat.mul_ne_zero
        . omega
        .
          rw [← Nat.pos_iff_ne_zero]
          apply Nat.pow_pos
          omega
      intro n hn


      grw [Finset.card_le_card (t := (S ^ max_len) ^ n)]

      .
        rw [← pow_mul]
        grw [s_poly _ (by exact Right.one_le_mul start_pos_nonzero hn)]
        rw [mul_pow]
        rw [← mul_assoc]
      .
        intro s' hs'

        have S'_subset_s_pow: S' ⊆ (S ^ max_len) := by
          intro a a'


          let exists_list := (weak_mem_closure_prod_list S a (by
            simp [S_generates]
          ))
          let l := exists_list.choose
          have l_prop := exists_list.choose_spec

          have len_le_max: l.length ≤ max_len := by
            unfold max_len
            apply le_sup
            simp [all_lists]
            use a
            use a'


          let foo := Fin.append (fun i => l[i].val) (fun (i: Fin (max_len - l.length)) => 1)
          rw [Finset.mem_pow]
          use (fun i => ⟨(foo ⟨i.val, by omega⟩), by (
            unfold foo
            simp
            unfold Fin.append
            unfold Fin.addCases
            simp
            split_ifs
            .
              rename_i i_lt
              have l_i_prop := l[i].property
              nth_rw 2 [S_symm] at l_i_prop
              simp at l_i_prop
              exact l_i_prop
            . apply S_one
          )⟩)
          conv =>
            rhs
            rw [← l_prop]
          unfold foo
          simp
          have add_sub: max_len = l.length + (max_len - l.length)  := by omega
          rw [List.ofFn_congr add_sub]
          simp
          rfl

        have pow_subset := Finset.pow_subset_pow S'_subset_s_pow (m := n) (n := n) (by
          have S_subset: S^1 ⊆ S^max_len := by
            apply Finset.pow_subset_pow
            . simp
            . apply S_one
            . omega

          simp at S_subset
          exact S_subset S_one
        ) (by omega)

        exact pow_subset hs'
  .
    rw [← not_subsingleton_iff_nontrivial] at g_nontrivial
    simp at g_nontrivial
    use 1
    refine ⟨by simp, ?_⟩
    intro n hn
    simp
    grw [Finset.card_pow_le]
    grw [Finset.card_le_one_of_subsingleton]
    simp
    exact Nat.one_le_pow d n hn


-- Lemma 3.31 (Volume Packing)
end

theorem solution.{u_1} : type_of% @poly_growth_equiv_oai.{u_1} := @poly_growth_equiv_oai.{u_1}

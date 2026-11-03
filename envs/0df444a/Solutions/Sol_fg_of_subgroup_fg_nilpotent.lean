-- Prove2me | solution 1 for fg_of_subgroup_fg_nilpotent
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T23:17:30.289173+00:00
-- url     : https://prove2.me/submissions/ccf664dd-9ed6-413e-bbb5-583aa0010c31

import Mathlib
import Definitions.Def_OAIQ093D005

section
-- module Solutions.OAIQ093_PR.ToMathlib_GroupTheory_Closure
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Subgroup closures

General-purpose material extracted from the Gromov development, destined for mathlib.
-/


open scoped Pointwise Finset

lemma closure_set_union_normal {G: Type*} [Group G] (S: Set G) (N: Subgroup G) (hN: N.Normal) {x: G} (hx: x ∈ Subgroup.closure (S ∪ N)):
  ∃ a: N, ∃ l: List ↑(S ∪ S⁻¹), x = l.unattach.prod * a := by

  induction hx using Subgroup.closure_induction with
  | one =>
    use 1
    use []
    simp
  | mem y hy =>
    simp at hy
    cases hy
    .
      rename_i y_mem_S
      use 1
      use [⟨y, by simp [y_mem_S]⟩]
      simp
    . rename_i y_mem_N
      use ⟨y, y_mem_N⟩
      use []
      simp
  | mul y z hy hz y_eq z_eq =>
    obtain ⟨a, l, y_eq⟩ := y_eq
    obtain ⟨b, m, z_eq⟩ := z_eq
    simp [y_eq, z_eq]
    group
    use ((m.unattach.prod⁻¹) * a * (m.unattach.prod)⁻¹⁻¹ * b)
    refine ⟨(by
      apply Subgroup.mul_mem
      . apply hN.conj_mem a (by simp)
      . simp
    ), ?_⟩
    use (l ++ m)
    simp
    group
  | inv y hy a_eq =>
    obtain ⟨a, l, y_eq⟩ := a_eq
    use ⟨_, hN.conj_mem a⁻¹ (by simp) l.unattach.prod⟩
    simp
    use (l.map (fun x => ⟨x⁻¹, (by
      simp
      have x_prop := x.prop
      simp [-Subtype.coe_prop] at x_prop
      grind
    )⟩)).reverse
    nth_rw 1 [y_eq]
    simp
    conv =>
      arg 2
      arg 1
      equals l.unattach.prod⁻¹ =>
        rw [List.prod_inv_reverse]
        congr
        ext i g
        simp
    group
end

section
-- module Solutions.OAIQ093_PR.Unipotent_Commutator
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

/-!
# Iterated commutators and the lower central series

`iteratedCommutator`, the generating sets `iterate_comm_set`, and
`lower_central_generates_succ`.
-/


set_option linter.style.longLine false
set_option linter.style.commandStart false
set_option linter.style.cdot false

open scoped commutatorElement IsMulCommutative Pointwise


lemma comm_prod {G: Type*} [Group G] (x y z: G): ⁅x * y, z⁆ = ⁅x, ⁅y, z⁆⁆ * ⁅y, z⁆ * ⁅x, z⁆ := by
  simp [Bracket.bracket]
  group


-- Lemma 13.30 (3)
lemma comm_prod_right {G: Type*} [Group G] (x y z: G): ⁅x, y * z⁆ = ⁅x, y⁆ * ⁅y, ⁅x, z⁆⁆ * ⁅x, z⁆ := by
  simp [Bracket.bracket]
  group


lemma comm_first_inv {G: Type*} [Group G] (x y: G): ⁅x⁻¹, y⁆ = ⁅x⁻¹, ⁅y, x⁆⁆ * ⁅y, x⁆ := by
  simp [Bracket.bracket]
  group

-- Each element of G can be written as a product of elements of S in at least one way
lemma new_mem_S_prod_list {G: Type*} [Group G] {S: Set G} {x: G} (hx: x ∈ Subgroup.closure S): ∃ l: List ↑(S ∪ S⁻¹), l.unattach.prod = x:= by
  -- https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/Group.20.28.2FMonoid.2Fetc.29.20closures.20are.20a.20finite.20product.2Fsum/near/477951441
  have foo := Submonoid.exists_list_of_mem_closure (s := S ∪ S⁻¹) (x := x)
  rw [← Subgroup.closure_toSubmonoid _] at foo
  simp at foo
  specialize foo hx
  obtain ⟨l, ⟨mem_s, prod_eq⟩⟩ := foo
  use (l.attach).map (fun x => ⟨x.val, mem_s (x.val) x.property⟩)
  unfold List.unattach
  simp [prod_eq]


lemma double_comm_mem {G: Type*}  [DecidableEq G] [Group G] (S: Finset G) {l': G} (n: ℕ) (ih: (⊤ : Subgroup G).lowerCentralSeries n = Subgroup.closure (iterate_comm_set (S ∪ S⁻¹) n ∪ ↑((⊤ : Subgroup G).lowerCentralSeries (n + 1)))) (g': ↑(S ∪ S⁻¹))  (l'_mem: l' ∈ ↑(iterate_comm_set (S ∪ S⁻¹) n ∪ (iterate_comm_set (S ∪ S⁻¹) n)⁻¹)): ⁅l'⁻¹, ⁅g'.val, l'⁆⁆ ∈ Subgroup.closure (iterate_comm_set (S ∪ S⁻¹) (n + 1) ∪ ↑((⊤ : Subgroup G).lowerCentralSeries (n + 1 + 1))) := by
  rw [← Subgroup.inv_mem_iff]
  simp
  apply Subgroup.mem_closure_of_mem
  apply Set.mem_union_right
  simp [mem_lowerCentralSeries_succ_iff]
  apply Subgroup.mem_closure_of_mem
  simp
  use ⁅g'.val, l'⁆
  refine ⟨?_, ?_⟩
  .

    rw [← Subgroup.inv_mem_iff]
    simp
    apply Subgroup.mem_closure_of_mem
    simp
    use l'
    refine ⟨?_, ?_⟩
    . rw [ih]
      simp at l'_mem
      cases l'_mem
      .
        rename_i l'_mem_forward
        apply Subgroup.mem_closure_of_mem
        apply Set.mem_union_left
        exact l'_mem_forward
      . rename_i l'_mem_inv
        rw [← Subgroup.closure_inv]
        apply Subgroup.mem_closure_of_mem
        simp
        left
        exact l'_mem_inv
    .
      use g'
  .
    use l'⁻¹


set_option maxHeartbeats 400000 in
lemma triple_comm_mem {G: Type*} [Group G] [DecidableEq G] (S: Finset G) {l': G} (n: ℕ) (ih: (⊤ : Subgroup G).lowerCentralSeries n = Subgroup.closure (iterate_comm_set (S ∪ S⁻¹) n ∪ ↑((⊤ : Subgroup G).lowerCentralSeries (n + 1)))) (g': ↑(S ∪ S⁻¹))   (l'_mem_comm: l' ∈ iterate_comm_set (S ∪ S⁻¹) n ∨ l'⁻¹ ∈ iterate_comm_set (S ∪ S⁻¹) n):  ⁅l'⁻¹, ⁅g'.val, l'⁆⁆ * ⁅g'.val, l'⁆ ∈  Subgroup.closure (iterate_comm_set (S ∪ S⁻¹) (n + 1) ∪ ↑((⊤ : Subgroup G).lowerCentralSeries (n + 1 + 1))) := by


  have g'_prop := g'.prop
  rw [Finset.mem_union] at g'_prop


  cases l'_mem_comm
  .
    rw [← Subgroup.inv_mem_iff]
    simp
    rename_i l'_mem
    . apply Subgroup.mul_mem
      .
        apply Subgroup.mem_closure_of_mem
        apply Set.mem_union_left
        simp [iterate_comm_set]
        use g'
        refine ⟨by simpa using g'_prop, ?_⟩
        use l'
      .
        rw [← Subgroup.inv_mem_iff]
        simp
        apply double_comm_mem
        . exact ih
        . simp [l'_mem]

  .

    rename_i l'_inv_mem
    . apply Subgroup.mul_mem
      .
        apply double_comm_mem
        exact ih
        simp [l'_inv_mem]


      .
        rw [← Subgroup.inv_mem_iff]
        simp
        conv =>
          arg 2
          arg 1
          equals l'⁻¹⁻¹ => simp

        rw [comm_first_inv]
        simp
        apply Subgroup.mul_mem
        .
          have foo := double_comm_mem (l' := l'⁻¹ ) _ _ ih g' (by
            simp
            left
            exact l'_inv_mem
          )
          simp at foo
          exact foo
        .
          rw [← Subgroup.inv_mem_iff]
          simp
          apply Subgroup.mem_closure_of_mem
          apply Set.mem_union_left
          simp [iterate_comm_set]
          use g'
          simp at g'_prop
          simp [g'_prop]
          use l'⁻¹


set_option maxHeartbeats 400000 in
lemma lower_central_generates_succ {G: Type*} [Group G] [DecidableEq G] (S: Finset G) (hS: Subgroup.closure (S: Set G) = ⊤) (n: ℕ):
  (⊤ : Subgroup G).lowerCentralSeries n = Subgroup.closure ((iterate_comm_set (S ∪ S⁻¹) n) ∪ ↑((⊤ : Subgroup G).lowerCentralSeries (n + 1))) := by
    induction n with
    | zero =>
      simp [iterate_comm_set]
      rw [Subgroup.closure_union]
      rw [Subgroup.closure_union]
      simp [hS]
    | succ n ih =>
      ext a
      refine ⟨?_, ?_⟩
      .
        intro ha
        rw [mem_lowerCentralSeries_succ_iff] at ha
        apply (Subgroup.closure_le _).mp ?_ ha
        simp
        intro p hp
        simp at hp
        obtain ⟨c, c_mem, ⟨g, p_eq_comm⟩⟩ := hp
        rw [← p_eq_comm]
        rw [ih] at c_mem

        have h_c_prod := closure_set_union_normal (S := iterate_comm_set (S ∪ S⁻¹) n) (N := (⊤ : Subgroup G).lowerCentralSeries (n + 1)) (by
          infer_instance
        ) c_mem
        obtain ⟨x, l, c_prod⟩ := h_c_prod
        rw [c_prod]
        rw [comm_prod]

        have x_comm_mem: ⁅x.val, g⁆ ∈ (⊤ : Subgroup G).lowerCentralSeries (n + 1 + 1) := by
          rw [mem_lowerCentralSeries_succ_iff]
          apply Subgroup.mem_closure_of_mem
          simp
          use x
          exact ⟨x.2, g, rfl⟩


        apply Subgroup.mul_mem
        . apply Subgroup.mul_mem
          .

            conv =>
              arg 2
              equals l.unattach.prod * ⁅x.val, g⁆ * l.unattach.prod⁻¹ * ⁅x.val, g⁆⁻¹ =>
                simp [Bracket.bracket]


            apply Subgroup.mul_mem
            .
              apply Subgroup.mem_closure_of_mem
              apply Set.mem_union_right
              simp
              apply Subgroup.Normal.conj_mem
              . infer_instance
              . exact x_comm_mem
            .
              apply Subgroup.mem_closure_of_mem
              apply Set.mem_union_right
              simp only [SetLike.mem_coe]
              rw [Subgroup.inv_mem_iff]
              apply x_comm_mem
          .
            apply Subgroup.mem_closure_of_mem
            apply Set.mem_union_right
            simp only [SetLike.mem_coe]
            apply x_comm_mem
        .
          obtain ⟨g_list, g_prod⟩ := new_mem_S_prod_list (S := S) (x := g) (by simp [hS])
          --clear ha a p_eq_comm p c_prod c_mem c x_comm_mem
          rw [← g_prod]
          clear g_prod c_prod


          -- TODO - figure out how to get Nat.le_induction working
          induction h_len: g_list.unattach.length + l.unattach.length using Nat.case_strong_induction_on generalizing g_list l with
          | hz =>
            simp at h_len
            obtain ⟨g_list_eq, l_eq⟩ := h_len
            simp [g_list_eq, l_eq]
          | hi k hk =>


            by_cases g_list_zero: g_list.length = 0
            . simp at g_list_zero
              simp [g_list_zero]
            .
              simp at g_list_zero


              by_cases l_len_ne_zero: l.unattach.length = 0
              . have l_empty: l.unattach = [] := by
                  exact List.eq_nil_iff_length_eq_zero.mpr l_len_ne_zero
                simp [l_empty]


              by_cases both_eq_one: g_list.length = 1 ∧ l.unattach.length = 1
              .
                obtain ⟨g_len_one, l_len_one⟩ := both_eq_one
                obtain ⟨g', h_g'⟩ := List.length_eq_one_iff.mp g_len_one
                obtain ⟨l', h_l'⟩ := List.length_eq_one_iff.mp l_len_one

                simp [h_g', h_l']

                conv =>
                  arg 2
                  arg 1
                  equals l'⁻¹⁻¹ => simp


                have l'_mem: l' ∈ l.unattach := by
                  simp [h_l']

                rw [List.mem_unattach] at l'_mem
                obtain ⟨l'_mem_comm, l'_subtype_mem⟩ := l'_mem
                simp at l'_mem_comm

                rw [comm_first_inv]
                simp
                have foo := triple_comm_mem (l' := l'⁻¹) _ _ ih ⟨g', by (
                  have foo := g'.prop
                  simp [-Subtype.coe_prop] at foo
                  simp
                  exact foo
                )⟩  (by
                  simp
                  grind
                )
                simp at foo
                exact foo


              rw [not_and_or] at both_eq_one
              cases both_eq_one
              . rename_i g_len_ne_one

                have g_len_ne_zero: g_list.length ≠ 0 := by
                  simp
                  exact g_list_zero
                have two_le_g_len: 2 ≤ g_list.length := by
                  omega

                clear g_len_ne_one g_len_ne_zero
                simp at h_len


                rw [← List.take_append_getLast (l := g_list) (g_list_zero)]
                rw [List.unattach_append]
                simp
                rw [comm_prod_right]
                . apply Subgroup.mul_mem
                  . apply Subgroup.mul_mem
                    .

                      have prev := hk k (by simp) l (List.take (g_list.length - 1) g_list) (by
                        simp
                        omega
                      )
                      exact prev
                    .


                      rw [← Subgroup.inv_mem_iff]
                      simp
                      apply Subgroup.mem_closure_of_mem
                      apply Set.mem_union_right
                      simp only [SetLike.mem_coe]
                      have l_prod_mem : l.unattach.prod ∈ (⊤ : Subgroup G).lowerCentralSeries n := by
                        rw [ih]
                        apply Subgroup.list_prod_mem
                        intro x hx
                        simp at hx
                        obtain ⟨x_mem, x_subtype_mem⟩ := hx
                        cases x_mem
                        . rename_i x_mem_forward
                          apply Subgroup.mem_closure_of_mem
                          grind
                        . rename_i x_mem_inv
                          rw [← Subgroup.closure_inv]
                          apply Subgroup.mem_closure_of_mem
                          simp
                          left
                          exact x_mem_inv
                      exact Subgroup.commutator_mem_commutator
                        (Subgroup.commutator_mem_commutator l_prod_mem (Subgroup.mem_top _))
                        (Subgroup.mem_top _)
                  .

                    have prev := hk (l.length + 1) (by omega) l [(g_list.getLast g_list_zero)] (by
                      simp
                      omega
                    )
                    simp at prev
                    exact prev

              .
                rename_i l_len_ne_one
                simp at l_len_ne_one
                have l_ne_zero: l.length ≠ 0 := by
                  rw [List.length_unattach] at l_len_ne_zero
                  exact l_len_ne_zero

                simp [-List.length_eq_zero_iff] at l_ne_zero
                have two_le_l_len: 2 ≤ l.length := by
                  omega

                rw [← List.take_append_getLast (l := l) (by simpa using l_ne_zero)]
                rw [List.unattach_append]
                simp
                rw [comm_prod]
                simp at h_len
                apply Subgroup.mul_mem
                . apply Subgroup.mul_mem
                  .
                    rw [← Subgroup.inv_mem_iff]
                    simp
                    apply Subgroup.mem_closure_of_mem
                    apply Set.mem_union_right
                    simp only [SetLike.mem_coe]
                    have last_mem : (l.getLast (by simpa using l_ne_zero)).val ∈
                        (⊤ : Subgroup G).lowerCentralSeries n := by
                      rw [ih]
                      have l_prop := (l.getLast (by simpa using l_ne_zero)).prop
                      rw [Set.mem_union] at l_prop
                      cases l_prop
                      . rename_i l_prop_forward
                        apply Subgroup.mem_closure_of_mem
                        grind
                      . rename_i l_prop_inv
                        rw [← Subgroup.closure_inv]
                        simp
                        apply Subgroup.mem_closure_of_mem
                        grind
                    exact Subgroup.commutator_mem_commutator
                      (Subgroup.commutator_mem_commutator last_mem (Subgroup.mem_top _))
                      (Subgroup.mem_top _)
                  .

                    have foo := hk (g_list.length + 1) (by omega) [l.getLast (by simpa using l_ne_zero)] g_list (by simp)
                    simp at foo
                    exact foo
                .
                  have foo := hk k (by simp) (List.take (l.length - 1) l) g_list (by
                    simp
                    omega
                  )
                  exact foo

      intro ha
      rw [mem_lowerCentralSeries_succ_iff]


      have closure_le: (Subgroup.closure ((iterate_comm_set (S ∪ S⁻¹) (n + 1)) ∪ ↑((⊤ : Subgroup G).lowerCentralSeries (n + 1 + 1)))) ≤ (Subgroup.closure {x | ∃ p ∈ (⊤ : Subgroup G).lowerCentralSeries n, ∃ q ∈ (⊤ : Subgroup G), ⁅p, q⁆ = x}) := by
        rw [Subgroup.closure_le]
        intro x hx
        simp at hx
        cases hx
        .
          rename_i x_mem_comm
          apply Subgroup.mem_closure_of_mem
          simp
          rw [ih]
          simp [iterate_comm_set] at x_mem_comm
          obtain ⟨s, s_mem, ⟨c, c_mem, c_comm⟩⟩ := x_mem_comm
          use c
          refine ⟨?_, ?_⟩
          . apply Subgroup.mem_closure_of_mem
            grind
          . use s
        .
          rename_i x_mem_lower_two
          have x_mem_lower_succ: x ∈ (⊤ : Subgroup G).lowerCentralSeries (n + 1) :=
            Subgroup.commutator_le_left _ _ x_mem_lower_two


          rw [mem_lowerCentralSeries_succ_iff] at x_mem_lower_succ
          simpa using x_mem_lower_succ


      apply closure_le ha
end

section
-- module Solutions.OAIQ093_PR.Unipotent_FG
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
attribute [-simp] _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

/-!
# Finite generation of subgroups

That subgroups of finitely generated abelian and nilpotent groups are finitely generated, plus
the supporting transfer lemmas along homomorphisms.
-/


set_option linter.style.longLine false
set_option linter.style.commandStart false
set_option linter.style.cdot false

open scoped commutatorElement IsMulCommutative Pointwise

variable {G: Type*} [Group G] [DecidableEq G] (S: Finset G)

variable {G: Type*} [Group G] [DecidableEq G] (S: Finset G)


-- TODO - generalize and pr to mathlib
lemma fg_of_subgroup_fg_comm {A : Type*} [CommGroup A] [Group.FG A] (H : Subgroup A) : H.FG := by
  rw [Subgroup.fg_iff_add_fg]
  have : Module.Finite ℤ (Additive A) := Module.Finite.iff_addGroup_fg.mpr inferInstance
  have h := IsNoetherian.noetherian (R := ℤ) (AddSubgroup.toIntSubmodule H.toAddSubgroup)
  rw [Submodule.fg_iff_addSubgroup_fg] at h
  simpa using h

lemma fg_extension {A: Type*} [Group A] (N: Subgroup A) [N.Normal] (hN: N.FG) (hQ: Group.FG (A ⧸ N)): Group.FG A := by
  classical
  obtain ⟨S_Q, hS_Q⟩ := hQ
  obtain ⟨S_N, hS_N⟩ := hN
  let SQ_out := Finset.image (fun (a: (A ⧸ N)) => a.out) S_Q
  have SQ_eq: S_Q = Finset.image (QuotientGroup.mk' _) SQ_out := by
    simp [SQ_out]
    ext a
    simp

  rw [Group.fg_def, Subgroup.fg_iff]
  rw [SQ_eq] at hS_Q
  use S_N ∪ SQ_out
  refine ⟨?_, ?_⟩
  .
    simp [SQ_out]
    rw [Subgroup.closure_union]
    simp [hS_N]
    ext a
    simp
    by_cases mem_N: a ∈ N
    . apply Subgroup.mem_sup_left
      exact mem_N
    .
      let a_map: (A ⧸ N) := a
      have a_mem_top: a_map ∈ (⊤ : Subgroup (A ⧸ N)) := by
        simp

      rw [← hS_Q] at a_mem_top
      simp only [Finset.coe_image] at a_mem_top
      rw [← MonoidHom.map_closure] at a_mem_top
      simp at a_mem_top
      obtain ⟨k, hk⟩ := a_mem_top
      simp [SQ_out] at hk
      simp [a_map] at hk
      have a_eq := hk.2
      rw [QuotientGroup.eq] at a_eq
      rw [← Subgroup.mul_mem_cancel_left (x := k⁻¹)]
      .
        apply Subgroup.mem_sup_left
        exact a_eq
      . apply Subgroup.mem_sup_right
        simp
        exact hk.1

  . simp

lemma fg_domain_of_ker_range {A B: Type*} [Group A] [Group B] (f : A →* B) (hA: Subgroup.FG f.ker) (hB: Subgroup.FG f.range): Group.FG A := by
  have new_fg := fg_extension (f.ker) hA
  apply new_fg
  have equiv := QuotientGroup.quotientKerEquivRange f
  rw [← Group.fg_iff_subgroup_fg] at hB
  apply Group.fg_of_surjective (f := equiv.symm.toMonoidHom)
  simp
  exact MulEquiv.surjective equiv.symm

lemma Group.FG.of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) (h : Group.FG G) :
    Group.FG H :=
  haveI := h
  Group.fg_of_surjective (f := e.toMonoidHom) e.surjective

set_option maxHeartbeats 5000000 in
lemma fg_of_subgroup_fg_nilpotent_oai {A: Type*} [DecidableEq A] [Group A] [Group.IsNilpotent A] (A_fg: Group.FG A) (H: Subgroup A): H.FG := by
  classical
  revert H
  induction hn: Group.nilpotencyClass A using Nat.strong_induction_on generalizing A with
  | h n ih =>
  match n with
  | 0 =>
    rw [Group.nilpotencyClass_zero_iff_subsingleton] at hn
    intro H
    have H_eq: H = ⊥ := by
      ext a
      simp
      simp [Subsingleton.eq_one a]
    simp [H_eq]
    exact fg_of_subgroup_fg_comm ⊥
  | n + 1 =>
    have comm_eq := Subgroup.lowerCentralSeries_succ (⊤ : Subgroup A) n
    rw [← hn] at comm_eq
    rw [Subgroup.lowerCentralSeries_nilpotencyClass] at comm_eq
    conv at comm_eq =>
      rhs
      simp
    rw [eq_comm, Subgroup.commutator_eq_bot_iff_le_centralizer] at comm_eq
    simp [Subgroup.centralizer_univ] at comm_eq
    have n_fg: (Subgroup.lowerCentralSeries (⊤ : Subgroup A) n).FG := by
      obtain ⟨S, hS⟩ := A_fg
      rw [lower_central_generates_succ (G := A) S hS]
      rw [← hn]
      simp
      rw [← Group.fg_iff_subgroup_fg]
      apply Group.closure_finset_fg

    specialize ih (A := A ⧸  (Subgroup.lowerCentralSeries (⊤ : Subgroup A) n)) (Group.nilpotencyClass (A ⧸ (⊤ : Subgroup A).lowerCentralSeries n)) (by
      -- The `n`-th term of the lower central series of `A ⧸ Cⁿ A` is the image of `Cⁿ A`, i.e. `⊥`.
      -- Hence that quotient has class `≤ n < n + 1 = nilpotencyClass A`.
      have key : (⊤ : Subgroup (A ⧸ (⊤ : Subgroup A).lowerCentralSeries n)).lowerCentralSeries n
          = ⊥ := by
        have hmap : Subgroup.map
            (QuotientGroup.mk' ((⊤ : Subgroup A).lowerCentralSeries n)) (⊤ : Subgroup A) = ⊤ :=
          Subgroup.map_top_of_surjective _ QuotientGroup.mk_surjective
        rw [← hmap, ← Subgroup.map_lowerCentralSeries, Subgroup.map_eq_bot_iff,
          QuotientGroup.ker_mk']
      have h_le := Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mp key
      omega
    ) (by infer_instance) rfl

    intro H
    have h_inf_fg: ((H ⊓ (⊤ : Subgroup A).lowerCentralSeries n).subgroupOf ((⊤ : Subgroup A).lowerCentralSeries n)).FG := by
      let c_comm := Group.commGroupOfCenterEqTop (G := ((⊤ : Subgroup A).lowerCentralSeries n)) (by
        rw [Subgroup.eq_top_iff']
        intro x
        rw [Subgroup.mem_center_iff]
        intro y
        have foo := comm_eq x.prop
        rw [Subgroup.mem_center_iff] at foo
        specialize foo y.val
        ext
        simpa using foo
      )
      rw [← Group.fg_iff_subgroup_fg] at n_fg
      apply fg_of_subgroup_fg_comm


    rw [← Group.fg_iff_subgroup_fg]
    apply fg_domain_of_ker_range ((QuotientGroup.mk' ((⊤: Subgroup A).lowerCentralSeries n)).comp H.subtype)
    .
      -- The kernel is `N.subgroupOf H = (H ⊓ N).subgroupOf H`, which is the same abstract group as
      -- `(H ⊓ N).subgroupOf N` — the version we proved FG using that `N` is abelian.
      rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk', Subgroup.comap_subtype,
        ← Subgroup.inf_subgroupOf_left, ← Group.fg_iff_subgroup_fg]
      exact Group.FG.of_mulEquiv
        ((Subgroup.subgroupOfEquivOfLe inf_le_right).trans
          (Subgroup.subgroupOfEquivOfLe inf_le_left).symm)
        ((Group.fg_iff_subgroup_fg _).mpr h_inf_fg)
    .
      -- The range is the image of `H` in `A ⧸ Cⁿ A`, which is FG by the induction hypothesis.
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
      exact ih (Subgroup.map (QuotientGroup.mk' _) H)
end

theorem solution.{u_3} : type_of% @fg_of_subgroup_fg_nilpotent_oai.{u_3} := @fg_of_subgroup_fg_nilpotent_oai.{u_3}

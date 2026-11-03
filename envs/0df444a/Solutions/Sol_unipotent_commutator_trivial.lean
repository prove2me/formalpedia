-- Prove2me | solution 1 for unipotent_commutator_trivial
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T23:28:01.888117+00:00
-- url     : https://prove2.me/submissions/09db6a49-1495-4923-9f95-bcdf0d50ace4

import Mathlib
import Definitions.Def_OAIQ093D005

section
-- module Solutions.OAIQ093_PR.ToMathlib_Data_List_Infix
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Infixes of lists

General-purpose material extracted from the Gromov development, destined for mathlib.
-/


open scoped Finset

-- TODO - should this use List.splitBy or List.splitOnP in some way?
-- TODO - cleanup the proof and upstream to mathlib
lemma list_adjacent_elements {A: Type*} (l: List A) (p: A → Bool) (n : ℕ):
    (∃ l', l' <:+: l ∧ n ≤ l'.length ∧ ∀ a ∈ l', p a) ∨ ((l.length - 1) / n) ≤ (l.countP (fun a => !(p a))):= by


  rw [or_iff_not_imp_left]
  intro no_adjacent_seq


  simp at no_adjacent_seq

  -- Strong induction on list lengths
  induction l using Nat.strongRecMeasure (f := List.length)
  case ind l ih =>
    by_cases non_matching: ∀ a ∈ l, p a
    .

      have len_lt: l.length < n := by
        by_contra!
        specialize no_adjacent_seq l (by
          simp
        ) this
        obtain ⟨a, a_mem, not_p_a⟩ := no_adjacent_seq
        specialize non_matching a a_mem
        grind

      have len_sub_lt: l.length - 1 < n := by
        omega

      apply Nat.div_eq_of_lt at len_sub_lt
      rw [len_sub_lt]
      simp
    .

      simp [-List.mem_cons] at non_matching
      obtain ⟨a, a_mem, not_p_a⟩ := non_matching

      have hn: 0 < n := by
        by_contra!
        specialize no_adjacent_seq [] (by
          simp
        ) (by
          simpa using this
        )
        simp at no_adjacent_seq

      have list_eq: l = (l.takeWhile p) ++ (l.dropWhile p) := by
        simp

      have takeWhile_lt_n: (l.takeWhile p).length < n := by
        by_contra!
        specialize no_adjacent_seq (l.takeWhile p) (by
          apply List.IsPrefix.isInfix
          apply List.takeWhile_prefix
        ) (this)

        obtain ⟨x, hx_mem, not_p_x⟩ := no_adjacent_seq
        apply List.mem_takeWhile_imp at hx_mem
        grind

      have count_p: l.countP (fun a => !(p a)) = (l.dropWhile p).countP (fun a => !(p a)) := by
        nth_rw 1 [list_eq]
        rw [List.countP_append]
        simp
        intro a ha
        apply List.mem_takeWhile_imp at ha
        exact ha


      have count_tail_eq: (l.dropWhile p).countP (fun a => !(p a)) = 1 + (l.dropWhile p).tail.countP (fun a => !(p a)) := by


        have dropWhile_not_nil: (l.dropWhile p) ≠ [] := by
          by_contra!
          rw [this] at list_eq
          simp at list_eq
          rw [list_eq] at a_mem
          apply List.mem_takeWhile_imp at a_mem
          grind

        apply List.exists_cons_of_ne_nil at dropWhile_not_nil
        obtain ⟨head, tail, h_eq⟩ := dropWhile_not_nil
        rw [h_eq]
        simp
        rw [List.countP_cons]
        simp

        have not_head := List.head?_dropWhile_not p l
        simp [h_eq] at not_head
        simp [not_head]
        rw [add_comm]


      rw [count_p]
      rw [count_tail_eq]

      have l_length_eq : l.length = (l.takeWhile p).length + (l.dropWhile p).length := by
        nth_rw 1 [list_eq]
        rw [List.length_append]

      by_cases l_len_le: l.length ≤ n
      . have l_len_sub: l.length - 1 < n := by
          omega

        apply Nat.div_eq_of_lt at l_len_sub
        rw [l_len_sub]
        simp
      .


        have drop_length: l.length - n < (l.dropWhile p).length := by
          omega

        have drop_tail_length: l.length - n  ≤ (l.dropWhile p).tail.length := by
          simp
          omega

        have ih_drop := ih (l.dropWhile p).tail (by
          simp
          omega
        ) (by
            intro x hx x_len
            have foo := no_adjacent_seq x ?_ x_len
            .
              obtain ⟨b, hb, not_p_b⟩ := foo
              use b
            .
              -- TODO - why can't grind figure this the main goal without help?

              have tail_sub: (l.dropWhile p).tail <:+: (l.dropWhile p) := by
                apply List.IsSuffix.isInfix
                apply List.tail_suffix

              grw [hx]
              grw [tail_sub]
              apply List.IsSuffix.isInfix
              apply List.dropWhile_suffix
        )

        rw [← ge_iff_le]
        grw [ih_drop.ge]
        grw [drop_tail_length.ge]
        conv =>
          arg 1
          equals 1 + (((l.length - 1) / n) - 1) =>
            rw [← Nat.sub_mul_div]
            simp
            rw [Nat.sub_right_comm]

        rw [Nat.add_sub_of_le]

        rw [Nat.one_le_div_iff hn]
        omega
end

section
-- module Solutions.OAIQ093_PR.ToMathlib_GroupTheory_Nilpotent
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Nilpotent groups

General-purpose material extracted from the Gromov development, destined for mathlib.
-/


-- TODO - can the injectivity requirement be removed?
lemma map_nilpotent {G H: Type*} [Group G] [Group H] (A: Subgroup G) (f: G →* H) (hf: Function.Injective f) (hG: Group.IsNilpotent A): Group.IsNilpotent (Subgroup.map f A) := by
  rw [← Group.isNilpotent_congr (Subgroup.equivMapOfInjective _ _ _)]
  . exact hG
  . exact hf
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


lemma iterate_comm_set_eq_fold {G: Type*} [Group G] [DecidableEq G] (S: Finset G) (n: ℕ):
    iterate_comm_set S n = { g | ∃ s: S, ∃ l: List S, l.length = n ∧ (l.unattach.foldr (fun acc s => ⁅s, acc⁆) s.val) = g } := by

  induction n with
  | zero =>
    simp [iterate_comm_set]
  | succ n ih =>
    simp [iterate_comm_set]
    ext g
    simp
    refine ⟨?_, ?_⟩
    .
      intro h
      obtain ⟨s, s_mem, ⟨x, x_mem, comm_eq⟩⟩ := h
      rw [← Finset.mem_coe] at x_mem
      rw [ih] at x_mem
      simp at x_mem
      obtain ⟨t, t_mem, l, l_len, l_fold_eq⟩ := x_mem
      use t
      refine ⟨t_mem, ?_⟩
      use (⟨s, s_mem⟩ :: l)
      refine ⟨?_, ?_⟩
      . grind
      .
        simp
        rw [← comm_eq]
        rw [← l_fold_eq]
    .
      intro h
      obtain ⟨t, t_mem, l, l_len, l_fold_eq⟩ := h
      have l_len_eq := l_len
      apply List.exists_cons_of_length_eq_add_one at l_len

      obtain ⟨head, tail, l_eq⟩ := l_len
      rw [l_eq] at l_fold_eq
      simp at l_fold_eq

      use head
      refine ⟨by simp, ?_⟩
      simp at ih


      have tail_len_eq: tail.length = n := by
        rw [l_eq] at l_len_eq
        simp at l_len_eq
        exact l_len_eq


      use List.foldr (fun x b ↦ ⁅b, x⁆) t tail.unattach
      refine ⟨?_, ?_⟩
      .
        rw [← Finset.mem_coe]
        rw [ih]
        simp
        use t
        refine ⟨t_mem, ?_⟩
        use tail
      . exact l_fold_eq
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


-- https://math.stackexchange.com/questions/4995327/group-in-the-lower-central-series-is-generated-by-conjugates-of-comutators-of-ge
lemma iterate_comm_generates (hS: Subgroup.closure (S: Set G) = ⊤) (n: ℕ):
  (Subgroup.normalClosure (iterate_comm_set (S) n)) = (⊤ : Subgroup G).lowerCentralSeries n := by
  induction n with
  | zero =>
    simp [iterate_comm_set]

    have closure_le: ⊤ ≤ Subgroup.closure (S : Set G) := by
      simp [hS]


    rw [eq_top_iff]
    grw [closure_le]
    apply Subgroup.closure_le_normalClosure
  | succ n ih =>
    simp [lowerCentralSeries]
    rw [le_antisymm_iff]
    refine ⟨?_, ?_⟩
    .
      simp [Subgroup.normalClosure]
      intro y hy
      simp [Group.conjugatesOfSet, iterate_comm_set] at hy
      obtain ⟨s, s_mem, ⟨c, c_mem, c_comm⟩⟩ := hy
      simp [conjugatesOf] at c_comm
      obtain ⟨x, x_mem⟩ := c_comm
      rw [← x_mem]
      apply Subgroup.Normal.conj_mem
      . infer_instance
      .
        apply Subgroup.commutator_mem_commutator
        .
          rw [← ih]
          apply Subgroup.mem_closure_of_mem
          simp [Group.conjugatesOfSet]
          use c
          refine ⟨c_mem, ?_⟩
          simp [conjugatesOf]
          use 1
          simp
        . simp
    .

      have image_commute: ∀ s ∈ S, ∀ g ∈ (iterate_comm_set (S) n), QuotientGroup.mk' (((Subgroup.normalClosure (iterate_comm_set (S) (n + 1))))) (s * g) = QuotientGroup.mk' (((Subgroup.normalClosure (iterate_comm_set (S) (n + 1))))) (g * s) := by
        intro s hs g hg
        simp
        rw [← QuotientGroup.mk_mul]
        rw [← QuotientGroup.mk_mul]
        rw [QuotientGroup.eq]
        simp [Subgroup.normalClosure]
        rw [← Subgroup.inv_mem_iff]
        simp
        rw [← Subgroup.closure_inv]
        apply Subgroup.mem_closure_of_mem
        simp [-Set.mem_inv, Group.conjugatesOfSet]
        simp only [conjugatesOf]
        use g * s * g⁻¹ * s⁻¹
        refine ⟨?_, ?_⟩
        . simp [iterate_comm_set]
          use s
          refine ⟨by simp [hs], ?_⟩
          use g
          refine ⟨hg, ?_⟩
          simp [Bracket.bracket]
        .
          simp
          use s⁻¹ * g⁻¹
          group

      have comm_subset_center: (QuotientGroup.mk' _) '' (iterate_comm_set (S) n) ⊆ ((Subgroup.center (G ⧸ ((Subgroup.normalClosure (iterate_comm_set (S) (n + 1)))))).carrier) := by
        intro x hx
        simp at hx
        obtain ⟨a, a_mem, hx⟩ := hx
        rw [Subgroup.mem_carrier]
        rw [Subgroup.mem_center_iff]
        intro b
        rw [← QuotientGroup.out_eq' (a := b)]
        rw [← hx]
        rw [← QuotientGroup.mk_mul]
        rw [← QuotientGroup.mk_mul]
        rw [QuotientGroup.eq]
        simp


        have b_mem_top: Quotient.out b ∈ (⊤ : (Subgroup G)) := by
          simp

        rw [← hS] at b_mem_top

        -- TODO - figure out how to get the 'induction' tactic working here
        apply Subgroup.closure_induction (p := fun y hy => a⁻¹ * y⁻¹ * (a * y) ∈ Subgroup.normalClosure (iterate_comm_set (S) (n + 1))) (hx := b_mem_top)
        .
          intro s hs
          have comm := image_commute s hs a a_mem
          simp at comm
          rw [← QuotientGroup.mk_mul] at comm
          rw [← QuotientGroup.mk_mul] at comm
          rw [QuotientGroup.eq] at comm
          simp at comm
          exact comm
        . simp
        . intro y hy z hz y_mem z_mem
          simp
          conv =>
            arg 2
            equals (a⁻¹ * hy⁻¹ * a * hy) * (hy⁻¹ * a⁻¹ * y⁻¹ * a * y * hy) =>
              group
          apply Subgroup.mul_mem
          . group
            group at z_mem
            exact z_mem
          .
            have foo := (Subgroup.normalClosure_normal).conj_mem _ y_mem hy⁻¹
            simp at foo
            group at foo
            group
            exact foo
        .
          intro y hy y_mem
          rw [← Subgroup.inv_mem_iff]
          simp
          have foo := (Subgroup.normalClosure_normal).conj_mem _ y_mem y
          group at foo
          group
          exact foo


      simp [Bracket.bracket]
      intro g hg
      simp at hg
      obtain ⟨a, a_mem, b, g_eq⟩ := hg
      have normal_le_center := Subgroup.normalClosure_le_normal comm_subset_center
      rw [← Subgroup.map_normalClosure] at normal_le_center
      rw [ih] at normal_le_center
      simp
      have a_mem_center := @normal_le_center a⁻¹ ?_
      .
        rw [Subgroup.mem_center_iff] at a_mem_center
        specialize a_mem_center (QuotientGroup.mk b⁻¹)
        rw [← QuotientGroup.mk_inv] at a_mem_center
        rw [← QuotientGroup.mk_mul] at a_mem_center
        rw [← QuotientGroup.mk_mul] at a_mem_center
        rw [QuotientGroup.eq] at a_mem_center
        simp at a_mem_center
        rw [← g_eq]
        group at a_mem_center
        group
        exact a_mem_center
      . simp
        use a


      simp
      exact QuotientGroup.mk_surjective

-- Lemma 13.55 from https://www.math.ucdavis.edu/~kapovich/EPR/ggt.pdf
lemma comm_trivial_implies_nilpotent {G: Type*} [DecidableEq G] [Group G] (S: Finset G) (hS: Subgroup.closure (S: Set G) = ⊤) (n: ℕ) (h_comm: iterate_comm_set (S) (n) = {1}):
    (⊤ : Subgroup G).lowerCentralSeries n = ⊥ := by

  rw [← iterate_comm_generates S hS n]
  rw [h_comm]
  simp [Subgroup.normalClosure]
  intro g hg
  simp [Group.conjugatesOfSet, conjugatesOf] at hg
  exact hg


lemma normal_comm_mem {G: Type*} [Group G] {N: Subgroup G} (N_normal: N.Normal) (a b: G) (ha: a ∈ N) :
  ⁅a, b⁆ ∈ N := by

  dsimp [Bracket.bracket]
  have conj_mem := N_normal.conj_mem a⁻¹ (by simp [ha]) b
  conv =>
    arg 2
    equals a * (b * a⁻¹ * b⁻¹) => group

  apply Subgroup.mul_mem
  . exact ha
  . exact conj_mem
end

section
-- module Solutions.OAIQ093_PR.UnipotentGromov
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
attribute [-simp] _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

/-!
# Triviality of the unipotent commutator

`unipotent_commutator_trivial`.

Root of the `Gromov.Unipotent` hierarchy.
-/


set_option linter.style.longLine false
set_option linter.style.commandStart false
set_option linter.style.cdot false

open scoped commutatorElement IsMulCommutative Pointwise

variable {G: Type*} [Group G] [DecidableEq G] (S: Finset G)

lemma normal_comm_mem_right {G: Type*} [Group G] {N: Subgroup G} (N_normal: N.Normal) (a b: G) (hb: b ∈ N) :
  ⁅a, b⁆ ∈ N := by

  dsimp [Bracket.bracket]
  have conj_mem := N_normal.conj_mem b (by simp [hb]) a
  conv =>
    arg 2
    equals (a * b * a⁻¹) * b⁻¹ => group

  apply Subgroup.mul_mem
  . exact conj_mem
  . simpa using hb


lemma iterated_mem_iterated_set {G: Type*} [DecidableEq G] [Group G] (base right: G) (S: Finset G) (base_mem: base ∈ S) (right_mem: right ∈ S) (n: ℕ): iteratedCommutator base right n ∈ iterate_comm_set S n := by
  induction n with
  | zero =>
    simp [iterate_comm_set, iteratedCommutator]
    exact base_mem
  | succ n ih =>
    conv =>
      arg 2
      equals ⁅iteratedCommutator base right n, right⁆ =>
        unfold iteratedCommutator
        rw [Function.iterate_succ']
        simp

    simp [iterate_comm_set]
    use right
    refine ⟨right_mem, ?_⟩
    use iteratedCommutator base right n


lemma comm_subgroup_mem {G: Type*} [DecidableEq G] [Group G] {H: Subgroup G} (S: Finset H) (n: ℕ):
  ↑(iterate_comm_set (Finset.image H.subtype  S) n) ⊆ (H: Set G) := by
    induction n with
    | zero =>
      simp [iterate_comm_set]
      intro h h_mem
      simp
    | succ n ih =>
      simp [iterate_comm_set]
      intro h h_mem h_mem_s
      intro a ha
      simp
      have a_mem := ih ha
      simp [Bracket.bracket]
      apply Subgroup.mul_mem
      . apply Subgroup.mul_mem
        . apply Subgroup.mul_mem
          . exact a_mem
          . exact h_mem
        . simp
          exact a_mem
      . simp
        exact h_mem


lemma iterate_comm_subgroup {G: Type*} [DecidableEq G] [Group G] {H: Subgroup G} (S: Finset H) (h: H) (n: ℕ):
  h ∈ (iterate_comm_set S n) ↔ h.val ∈ iterate_comm_set (Finset.image H.subtype S) n := by
    induction n generalizing h with
    | zero =>
      simp [iterate_comm_set]
    | succ n ih =>
      dsimp [iterate_comm_set]
      simp
      refine ⟨?_, ?_⟩
      .
        intro h_mem
        obtain ⟨b, b_mem, ⟨b_mem_S, a, h_eq⟩⟩ := h_mem
        obtain ⟨a_mem_h, a_mem_comm, h_eq_comm⟩ := h_eq
        use b
        use ?_
        . use a
          refine ⟨?_, ?_⟩
          .
            rw [ih] at a_mem_comm
            simp at a_mem_comm
            exact a_mem_comm
          . rw [← h_eq_comm]
            simp [Bracket.bracket]
        . use b_mem
      . intro data_mem
        obtain ⟨b, ⟨b_mem_H, b_mem_S⟩, ⟨a, a_mem_comm, h_eq⟩⟩ := data_mem
        use b
        use b_mem_H
        refine ⟨?_, ?_⟩
        . exact b_mem_S
        . use a
          use ?_
          . refine ⟨?_, ?_⟩
            .
              rw [ih]
              simp
              exact a_mem_comm
            .
              ext
              rw [← h_eq]
              simp [Bracket.bracket]
          .
            simp [Bracket.bracket] at h_eq
            have iterate_subset := comm_subgroup_mem S n a_mem_comm
            simpa using iterate_subset


-- TODO - upstream to mathlib
lemma list_foldr_replicate (A: Type*) (a b: A) (n: ℕ) (f: A → A → A) :
    List.foldr f a (List.replicate n b) = Nat.iterate (f b) n a := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    rw [List.replicate_succ]
    rw [List.foldr_cons]
    rw [ih]
    rw [Function.iterate_succ']
    rfl

lemma list_fold_comm_one {G: Type*} [Group G] (l: List G) :
    List.foldr (fun x y => ⁅y, x⁆) (1 : G) l = 1 := by
  induction l with
  | nil =>
    simp
  | cons head tail ih =>
    simp only [List.foldr_cons]
    rw [ih]
    simp

lemma nat_iterate_comm_one (G: Type*) [Group G] (g: G) (n: ℕ):
    (Nat.iterate (fun x => ⁅x, g⁆) n 1) = 1 := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    rw [Function.iterate_succ']
    simp
    rw [ih]
    simp

-- TODO - why can't linarith or omega find this?

lemma count_mem_group_implies_lowercentral {G: Type*} [Group G] {N': Subgroup G} [∀ a: G, Decidable (a ∈ N')] (N'_normal: N'.Normal) (l: List G) (g: G)
    (l_nonempty: l ≠ []) (count_ne_zero: (l.countP (fun a => decide (a ∈ N'))) ≠ 0):
    l.foldr (fun acc s ↦ ⁅s, acc⁆) g ∈ Subgroup.lowerCentralSeries N' ((l.countP (fun a => decide (a ∈ N'))) - 1) := by

  induction l with
  | nil =>
    simp at l_nonempty
  | cons head tail ih =>
    by_cases head_in_N': head ∈ N'
    .
      simp only [List.countP_cons, List.foldr_cons, head_in_N', decide_true, if_true,
        Nat.add_sub_cancel]
      by_cases tail_empty: tail = []
      .
        simp [tail_empty]
        apply normal_comm_mem_right N'_normal
        exact head_in_N'
      .

        by_cases count_eq_zero: (tail.countP (fun a => decide (a ∈ N'))) = 0
        .
          simp [count_eq_zero]
          apply normal_comm_mem_right N'_normal
          exact head_in_N'
        .
          have count_sub_eq: (tail.countP (fun a => decide (a ∈ N'))) = (tail.countP (fun a => decide (a ∈ N'))) - 1 + 1 := by
            omega

          rw [count_sub_eq]
          specialize ih (by simpa using tail_empty) count_eq_zero
          exact Subgroup.commutator_mem_commutator ih head_in_N'
    . rw [List.countP_cons]
      simp only [head_in_N', decide_false, Bool.false_eq_true, ↓reduceIte]


      have tail_nonempty: tail ≠ [] := by
        by_contra!
        simp [this] at count_ne_zero
        contradiction

      rw [List.countP_cons] at count_ne_zero
      simp only [head_in_N', decide_false, Bool.false_eq_true, ↓reduceIte] at count_ne_zero
      rw [add_zero] at count_ne_zero
      specialize ih tail_nonempty count_ne_zero
      rw [List.foldr_cons]
      apply normal_comm_mem
      . infer_instance
      . exact ih


-- `Subgroup.map_toSubmonoid` rewrites the `.carrier` predicate of `Subgroup.map`, which breaks the
-- `unattach`/commutator rewrites below. Disable it for this proof.
-- `Subgroup.coe_subtype` rewrites `⇑H.subtype` to `Subtype.val`, which desynchronises the index
-- type `↥(Finset.image (⇑H.subtype) S ∪ {gamma_alpha})` of `l`/`gamma_list` from the goal and makes
-- the `rw`s below fail on a motive that is only defeq at default transparency. Disable it too.
attribute [-simp] Subgroup.map_toSubmonoid Subgroup.coe_subtype in
lemma unipotent_commutator_trivial_oai {G: Type*} [DecidableEq G] [Group G] (H: Subgroup G) {N': Subgroup H} [H_normal: H.Normal] [N'_char: N'.Characteristic] [N'_nilpotent: Group.IsNilpotent N'] (gamma_alpha: G) (gamma_not_n: ¬(gamma_alpha ∈ (Subgroup.map (Subgroup.subtype _) N'))) (m: ℕ)
  (h_gamma_alpha: ∀ g ∈ N', iteratedCommutator g.val gamma_alpha m = 1)
  (S: Finset H) (hS: Subgroup.closure S = N'):
  Group.IsNilpotent (Subgroup.closure ((Finset.image (Subgroup.subtype _) S) ∪ {gamma_alpha})) := by

  classical

  by_cases m_eq: m = 0
  .
    simp [iteratedCommutator, m_eq] at h_gamma_alpha
    have N'_bot: N' = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      simpa using h_gamma_alpha


    let foo := Subgroup.closureCommGroupOfComm (k := (↑(Finset.image (⇑H.subtype) S) ∪ {gamma_alpha})) ?_
    .

      apply CommGroup.isNilpotent
    . intro x hx y hy
      by_cases S_empty: S = ∅
      . simp [S_empty] at hx hy
        grind
      .
        have S_eq: S = {1} := by
          simp only [N'_bot, Subgroup.closure_eq_bot_iff] at hS
          have S_subset: S ⊆ {1} := by
            grind
          grind
        simp [S_eq] at hx hy
        aesop
  -- `S` generates `N'`, so it lands inside `N'`, and its image inside `Subgroup.map H.subtype N'`.
  have S_sub_N': ∀ y ∈ S, y ∈ N' := by
    intro y hy
    rw [← hS]
    exact Subgroup.subset_closure hy
  have image_sub_map: ∀ g ∈ Finset.image (⇑H.subtype) S, g ∈ Subgroup.map H.subtype N' := by
    intro g hg
    rw [Finset.mem_image] at hg
    obtain ⟨y, hy, rfl⟩ := hg
    exact ⟨y, S_sub_N' y hy, rfl⟩

  have nilpotent_map: Group.IsNilpotent ↥(Subgroup.map H.subtype N') := by
    apply map_nilpotent
    . exact Subgroup.subtype_injective H
    . exact N'_nilpotent

  rw [nilpotent_iff_lowerCentralSeries]
  use ((1 + (Group.nilpotencyClass ↥(Subgroup.map H.subtype N'))) * (m + 1)) + 2

  apply comm_trivial_implies_nilpotent (S := Finset.image (fun (a: ↑((Finset.image (Subgroup.subtype _) S) ∪ {gamma_alpha})) => ⟨a.val, by (
    apply Subgroup.mem_closure_of_mem
    have a_prop := a.property
    simp at a_prop
    simp
    exact a_prop
  )⟩) Finset.univ)
  .


    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ]
    apply Subgroup.map_injective (Subgroup.subtype_injective _)
    rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    congr 1
    ext g
    simp only [Set.mem_image, Set.mem_range]
    constructor
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
      have h := y.property
      rw [Finset.mem_union] at h
      rcases h with h | h
      · exact Set.mem_union_left _ h
      · exact Set.mem_union_right _ (Finset.mem_singleton.mp h)
    · intro hg
      exact ⟨⟨g, by apply Subgroup.mem_closure_of_mem; exact hg⟩,
        ⟨⟨g, by simpa using hg⟩, rfl⟩, rfl⟩
  .
    ext a
    rw [iterate_comm_subgroup]

    -- The image of the attached generating set back down into `G` is the original
    -- `Finset.image H.subtype S ∪ {gamma_alpha}`.
    conv =>
      arg 1
      arg 1
      arg 1
      equals (Finset.image (⇑H.subtype) S) ∪ {gamma_alpha} =>
        rw [Finset.image_image, Finset.univ_eq_attach]
        exact Finset.attach_image_val

    refine ⟨?_, ?_⟩
    .
      intro a_mem
      rw [← Finset.mem_coe] at a_mem
      rw [iterate_comm_set_eq_fold] at a_mem
      simp only [Set.mem_setOf_eq] at a_mem
      obtain ⟨s, l, l_length, a_eq⟩ := a_mem

      -- TODO - extract this to its own lemma
      have subsequent_comm_one: ∀ g: N', ∀ k: ℕ, m ≤ k → iteratedCommutator g.val.val gamma_alpha k = 1 := by
        intro g k hk
        simp [iteratedCommutator]

        apply Nat.le.dest at hk
        obtain ⟨t, ht⟩ := hk
        rw [← ht]
        rw [Function.iterate_add_apply]
        simp [iteratedCommutator] at h_gamma_alpha

        -- Use the fact that N' is invariant to conjugation by gamma
        have comm_in_H: ∀ t: ℕ, (fun x ↦ ⁅x, gamma_alpha⁆)^[t] g ∈ H := by
          clear ht
          intro t
          induction t with
          | zero =>
            simp
          | succ t ih =>
            rw [Function.iterate_succ']
            simp
            apply normal_comm_mem
            . infer_instance
            . exact ih

        have comm_in_N': (fun x ↦ ⁅x, gamma_alpha⁆)^[t] g ∈ (Subgroup.map (Subgroup.subtype _) N') := by
          clear ht
          induction t with
          | zero =>
            simpa using g_mem
          | succ t ih =>
            simp_rw [Function.iterate_succ']
            simp only [Function.comp_apply, Subgroup.subtype_apply,
              Subtype.exists, exists_and_right, exists_eq_right]
            apply normal_comm_mem
            .
              infer_instance
            . exact ih

        simp at comm_in_N'
        obtain ⟨foo, bar⟩ := comm_in_N'
        specialize h_gamma_alpha _ (comm_in_H _) bar
        rw [h_gamma_alpha]


      have adjacent_or_count := list_adjacent_elements l (fun x => decide (x = gamma_alpha)) (m + 1)
      rw [l_length] at adjacent_or_count
      cases adjacent_or_count
      .
        rename_i adjancent_gamma
        obtain ⟨gamma_list, h_gamma_list, gamma_list_len, eq_gamma_alpha⟩ := adjancent_gamma

        have eq_gamma_alpha_unattach: ∀ b ∈ gamma_list.unattach, b = gamma_alpha := by
          intro b hb
          rw [List.mem_unattach] at hb
          obtain ⟨b_mem, other⟩ := hb
          specialize eq_gamma_alpha _ other
          simp at eq_gamma_alpha
          exact eq_gamma_alpha


        -- TODO - why isn't there List.ext for a ∈ l ?
        have gamma_list_eq: gamma_list.unattach = List.replicate gamma_list.unattach.length gamma_alpha := by
          apply List.eq_replicate_of_mem
          intro b hb
          specialize eq_gamma_alpha_unattach b hb
          simp at eq_gamma_alpha
          grind


        refine Finset.mem_singleton.mpr ?_
        ext
        rw [← a_eq]
        rw [List.IsInfix] at h_gamma_list
        obtain ⟨l_prefix, l_suffix, h_list_eq⟩ := h_gamma_list
        rw [← h_list_eq]
        simp only [List.unattach_append, List.foldr_append, OneMemClass.coe_one]
        rw [gamma_list_eq]
        rw [list_foldr_replicate]
        unfold iteratedCommutator at h_gamma_alpha
        unfold iteratedCommutator at subsequent_comm_one
        simp [] at subsequent_comm_one


        have s_mem := s.property
        rw [Finset.mem_union] at s_mem
        cases s_mem
        . rename_i s_mem_N'
          rw [subsequent_comm_one]
          . rw [list_fold_comm_one]
          .
            clear h_list_eq
            induction l_suffix with
            | nil =>
              simp at s_mem_N'
              obtain ⟨hs, s_mem⟩ := s_mem_N'
              simp
              exact hs
            | cons head tail ih =>
              simp
              apply normal_comm_mem
              . infer_instance
              . exact ih
          .
            clear h_list_eq
            rw [← Subgroup.mem_map_iff_mem (f := H.subtype) (Subgroup.subtype_injective H)]
            induction l_suffix with
            | nil =>
              simp at s_mem_N'
              obtain ⟨hs, s_mem⟩ := s_mem_N'
              simp
              use hs
              rw [← hS]
              exact Subgroup.subset_closure s_mem
            | cons head tail ih =>
              simp [-Subgroup.mem_map]
              apply normal_comm_mem (by infer_instance)
              exact ih
          . rw [List.length_unattach]
            omega
        .
          rename_i s_eq_gamma
          simp at s_eq_gamma
          rw [s_eq_gamma]

          have gamma_len_eq: gamma_list.unattach.length = gamma_list.unattach.length - 1 + 1 := by
            rw [List.length_unattach]
            omega

          rw [gamma_len_eq]
          simp

          clear h_list_eq

          -- TODO - this can be simplified a lot
          have fold_mem: ⁅List.foldr (fun acc s ↦ ⁅s, acc⁆) gamma_alpha l_suffix.unattach, gamma_alpha⁆ ∈ (((Subgroup.map (Subgroup.subtype _) N').carrier ∪ {gamma_alpha}) : Set G) := by
            induction l_suffix with
            | nil =>
              simp
            | cons head tail ih =>
              have head_prop := head.prop
              rw [Finset.mem_union] at head_prop

              cases head_prop
              .
                rename_i head_in_N
                rw [Set.mem_union] at ih
                apply Set.mem_union_left
                apply normal_comm_mem (by infer_instance)
                apply normal_comm_mem_right (by infer_instance)
                exact image_sub_map _ head_in_N
              . rename_i head_gamma
                simp at head_gamma
                cases ih
                . rename_i left
                  simp only [List.unattach_cons, List.foldr_cons]
                  rw [head_gamma]
                  apply Set.mem_union_left
                  apply normal_comm_mem (by infer_instance)
                  exact left
                .
                  rename_i right
                  apply Set.mem_union_left
                  simp at right
                  simp only [List.unattach_cons, List.foldr_cons]
                  rw [head_gamma]
                  rw [right]
                  simp

          rw [Set.mem_union] at fold_mem
          cases fold_mem
          . rename_i fold_in_N
            simp at fold_in_N
            rw [subsequent_comm_one]
            . rw [list_fold_comm_one]
            .
              obtain ⟨foo, bar⟩ := fold_in_N
              exact foo
            . obtain ⟨foo, bar⟩ := fold_in_N
              exact bar
            . omega
          . rename_i fold_eq_gamma
            simp at fold_eq_gamma
            rw [fold_eq_gamma]


            have gamma_sub_sub: gamma_list.length - 1 = gamma_list.length - 1 - 1 + 1 := by omega
            rw [gamma_sub_sub]
            rw [Function.iterate_succ]
            simp
            rw [nat_iterate_comm_one]
            rw [list_fold_comm_one]

      .
        rename_i count_not_gamma
        simp at count_not_gamma
        rw [mul_comm] at count_not_gamma
        rw [Nat.mul_add_div] at count_not_gamma
        rw [Nat.div_eq_of_lt] at count_not_gamma
        . simp at count_not_gamma

          refine Finset.mem_singleton.mpr ?_
          ext
          rw [← a_eq]

          conv at count_not_gamma =>
            arg 2
            arg 1
            equals (fun (a: ↥(Finset.image (⇑H.subtype) S ∪ {gamma_alpha})) => decide (a.val ∈ (((Subgroup.map (Subgroup.subtype _) N'))))) =>
              ext x
              simp
              rw [← decide_not]
              congr
              simp
              refine ⟨?_, ?_⟩
              . intro hx other
                rw [← hx] at gamma_not_n
                simp at gamma_not_n
                apply gamma_not_n other
              . intro hx
                have x_prop := x.prop
                rw [Finset.mem_union] at x_prop
                simp [hx] at x_prop
                cases x_prop
                . rename_i mem_N'
                  obtain ⟨mem_H, mem_N⟩ := mem_N'
                  exact absurd (S_sub_N' _ mem_N) (hx mem_H)
                . rename_i x_eq
                  exact x_eq


          rw [add_comm] at count_not_gamma

          conv at count_not_gamma =>
            arg 2
            -- TODO - clean up and upstream to mathlib
            equals l.unattach.countP (fun a => decide (a ∈ (((Subgroup.map (Subgroup.subtype _) N'))))) =>
              clear count_not_gamma l_length a_eq
              rw [show l.unattach = l.map (·.val) from rfl, List.countP_map]; rfl


          have foo := count_mem_group_implies_lowercentral (N' := (Subgroup.map H.subtype N')) (by infer_instance) l.unattach s ?_ ?_
          .
            rw [Subgroup.lowerCentralSeries_eq_bot_of_nilpotencyClass_le (by omega)] at foo
            simpa using foo

          .
            -- TODO - this is ridiculously overcomplicated

            have l_len_ne: l.length ≠ 0 := by
              omega


            grind
          . omega
        . omega
        . omega
    .
      intro a_eq
      replace a_eq : a = 1 := Finset.mem_singleton.mp a_eq
      -- `S` need not contain `1`, so start the iterated commutator at `gamma_alpha`
      -- instead: `⁅gamma_alpha, gamma_alpha⁆ = 1`, and the remaining iterations stay at `1`.
      have iterate_mem := iterated_mem_iterated_set gamma_alpha gamma_alpha
        (Finset.image (⇑H.subtype) S ∪ {gamma_alpha}) (by simp) (by simp)
        ((1 + ((Group.nilpotencyClass ↥(Subgroup.map H.subtype N')))) * (m + 1) + 2)
      have comm_one : iteratedCommutator gamma_alpha gamma_alpha
          ((1 + ((Group.nilpotencyClass ↥(Subgroup.map H.subtype N')))) * (m + 1) + 2) = 1 := by
        unfold iteratedCommutator
        rw [Function.iterate_add_apply]
        simp [nat_iterate_comm_one]
      rw [comm_one] at iterate_mem
      rw [a_eq]
      simpa using iterate_mem
end

theorem solution.{u_2} : type_of% @unipotent_commutator_trivial_oai.{u_2} := @unipotent_commutator_trivial_oai.{u_2}

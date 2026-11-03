-- Prove2me | solution 1 for volume_packing
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T23:29:30.398853+00:00
-- url     : https://prove2.me/submissions/16d7ff30-02cb-4bc8-9040-849eeba785e4

import Mathlib
import Definitions.Def_OAIQ093D000

section
-- module Solutions.OAIQ093_PR.Unitary_Basic
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant
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


lemma unitary_preimage (n : ℕ) :
    (fun (m : Matrix (Fin n) (Fin n) ℂ) => m * (star m)) ⁻¹' {1} =
    (Matrix.unitaryGroup (Fin n) ℂ).carrier := by
  ext
  simp [Matrix.mem_unitaryGroup_iff]

lemma unitary_closed (n : ℕ) : IsClosed (Matrix.unitaryGroup (Fin n) ℂ).carrier := by
  rw [← unitary_preimage]
  apply IsClosed.preimage
  · fun_prop
  · simp


@[expose]
instance unitary_proper (n : ℕ) : ProperSpace ↥(Matrix.unitaryGroup (Fin n) ℂ) := by
  apply ProperSpace.of_isClosed
  apply unitary_closed


@[expose]
instance compact_unitary (n : ℕ) [Nonempty (Fin n)] :
    CompactSpace ↥(Matrix.unitaryGroup (Fin n) ℂ) := by
  rw [Metric.compactSpace_iff_isBounded_univ, Metric.isBounded_iff]
  use 2
  intro x _ y _
  rw [Subtype.dist_eq]
  grw [dist_le_norm_add_norm]
  rw [CStarRing.norm_coe_unitary, CStarRing.norm_coe_unitary]
  linarith


-- Lemma 3.31 (Volume Packing)
end

section
-- module Solutions.OAIQ093_PR.Unitary_Packing
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Volume packing in the unitary group

`volume_packing`, bounding how many almost-orthogonal translates fit in a ball, together with
the auxiliary inner product `FreshInnerProduct`.
-/


open scoped Matrix.Norms.L2Operator ComplexInnerProductSpace

set_option linter.style.longLine false
set_option linter.style.commandStart false

open Subgroup Pointwise Finset
open scoped Pointwise Finset
open scoped commutatorElement IsMulCommutative


set_option synthInstance.maxHeartbeats 100000 in
set_option maxHeartbeats 500000 in
open Pointwise in
lemma volume_packing_oai (n : ℕ) (hn : 0 < n) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ (G : Subgroup (Matrix.unitaryGroup (Fin n) ℂ)), (G' n ε G).FiniteIndex ∧ (G' n ε G).index ≤ C := by


  have nonempty_fin : Nonempty (Fin n) := by
    exact Fin.pos_iff_nonempty.mp hn

  let compacts_univ : TopologicalSpace.PositiveCompacts (Matrix.unitaryGroup (Fin n) ℂ) := {
    carrier := Set.univ,
    isCompact' := by apply CompactSpace.isCompact_univ
    interior_nonempty' := by
      simp
  }

  borelize ↥(Matrix.unitaryGroup (Fin n) ℂ)
  let measure_haar : MeasureTheory.MeasureSpace (Matrix.unitaryGroup (Fin n) ℂ) := {
    volume := MeasureTheory.Measure.haarMeasure compacts_univ
  }
  haveI hinv : (MeasureTheory.volume : MeasureTheory.Measure ↥(Matrix.unitaryGroup (Fin n) ℂ)).IsMulLeftInvariant := by
    show (MeasureTheory.Measure.haarMeasure compacts_univ).IsMulLeftInvariant
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  haveI hfin : MeasureTheory.IsFiniteMeasure (MeasureTheory.volume : MeasureTheory.Measure ↥(Matrix.unitaryGroup (Fin n) ℂ)) := by
    show MeasureTheory.IsFiniteMeasure (MeasureTheory.Measure.haarMeasure compacts_univ)
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  haveI hopen : (MeasureTheory.volume : MeasureTheory.Measure ↥(Matrix.unitaryGroup (Fin n) ℂ)).IsOpenPosMeasure := by
    show (MeasureTheory.Measure.haarMeasure compacts_univ).IsOpenPosMeasure
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

  use 1 / (MeasureTheory.volume (Metric.ball (1 : (Matrix.unitaryGroup (Fin n) ℂ) ) (ε / 2 / 2))).toReal

  intro G
  -- We can find a maximal subset I where ||a - b|| ≥ ε for distinct a, b in I
  let I_sets := { S | S ⊆ G.carrier ∧ ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ‖x.val - y.val‖ ≥ ε }
  have maximal_I := zorn_subset I_sets ?_
  · obtain ⟨I, hI⟩ := maximal_I
    have balls_cover : G.carrier ⊆ ⋃ (g ∈ I), Metric.ball g ε := by
      intro a ha
      by_cases a_dist_I : ∀ g ∈ I, ‖a.val - g.val‖ ≥ ε
      · have a_mem_I : a ∈ I := by
          have enlarge_I : {a} ∪ I ∈ I_sets := by
            simp [-Subtype.forall, I_sets]
            simp [Maximal] at hI
            have I_prop := hI.1
            simp [-Subtype.forall, I_sets] at I_prop
            refine ⟨?_, ?_⟩
            · apply Set.insert_subset ha I_prop.1
            · refine ⟨?_, ?_⟩
              · intro b hb a_neq_b
                apply a_dist_I b hb
              · intro c hc
                refine ⟨?_, ?_⟩
                · intro c_neq_a
                  rw [norm_sub_rev]
                  apply a_dist_I c hc
                · intro d hd c_neq_d
                  apply I_prop.2
                  · apply hc
                  · apply hd
                  · apply c_neq_d

          exact Maximal.mem_of_prop_insert hI enlarge_I

        · apply Set.mem_sUnion_of_mem (t := Metric.ball a ε)
          · simp [hε]
          · rw [Set.mem_range]
            use a
            -- TODO - this is a really weird way of doing this
            have nonempty_prop : Nonempty (a ∈ I) := by
              exact Nonempty.intro a_mem_I
            rw [Set.iUnion_const]
      · simp [-Subtype.forall, -Subtype.exists] at a_dist_I
        obtain ⟨b, b_mem, b_dist_le⟩ := a_dist_I
        rw [Set.mem_iUnion]
        use b
        simp [b_mem]
        rw [Subtype.dist_eq, dist_eq_norm_sub]
        exact b_dist_le
    -- Note - Vikman uses ε/2, but using ε/4 made things easier (it might actually be false for ε/2)
    have disjoint_balls : I.PairwiseDisjoint (fun g => Metric.ball g ((ε/2)/2)) := by
      intro a a_mem b b_mem a_neq_b
      simp [Maximal] at hI
      have I_prop := hI.1
      simp [-Subtype.forall, I_sets] at I_prop
      have dist_ge := I_prop.2 a a_mem b b_mem a_neq_b
      simp [Disjoint]
      intro X X_subset_A X_subset_B
      by_contra!
      obtain ⟨x, hx⟩ := this
      specialize X_subset_A hx
      specialize X_subset_B hx
      have triangle := dist_triangle a x b
      simp only [Metric.mem_ball, Subtype.dist_eq, dist_eq_norm_sub] at X_subset_A X_subset_B triangle
      rw [norm_sub_rev] at X_subset_A
      grw [X_subset_A, X_subset_B] at triangle
      simp at triangle
      linarith

    have translate_ball (d : ℝ) (hd : 0 < d) (g : (Matrix.unitaryGroup (Fin n) ℂ)): Metric.ball g d = (fun x => g * x) '' (Metric.ball (1 : (Matrix.unitaryGroup (Fin n) ℂ)) d) := by
      ext a
      rw [Set.mem_image, Metric.mem_ball]
      constructor
      · intro h
        refine ⟨g⁻¹ * a, ?_, by group⟩
        simp only [Metric.mem_ball, Subtype.dist_eq, dist_eq_norm_sub] at h ⊢
        have heq : ((g⁻¹ * a : Matrix.unitaryGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) - ((1 : Matrix.unitaryGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)
            = ((g⁻¹ : Matrix.unitaryGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) * ((a : Matrix (Fin n) (Fin n) ℂ) - (g : Matrix (Fin n) (Fin n) ℂ)) := by
          rw [mul_sub, ← Matrix.UnitaryGroup.mul_val, ← Matrix.UnitaryGroup.mul_val, inv_mul_cancel]
        rw [heq, CStarRing.norm_mem_unitary_mul _ (g⁻¹).2]
        exact h
      · rintro ⟨b, hb, rfl⟩
        simp only [Metric.mem_ball, Subtype.dist_eq, dist_eq_norm_sub] at hb ⊢
        have heq : ((g * b : Matrix.unitaryGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) - (g : Matrix (Fin n) (Fin n) ℂ)
            = (g : Matrix (Fin n) (Fin n) ℂ) * ((b : Matrix (Fin n) (Fin n) ℂ) - ((1 : Matrix.unitaryGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)) := by
          rw [mul_sub, ← Matrix.UnitaryGroup.mul_val]
          simp
        rw [heq, CStarRing.norm_mem_unitary_mul _ g.2]
        exact hb

    have volume_sum : MeasureTheory.volume (⋃ (g ∈ I), (Metric.ball g ((ε/2)/2))) ≤ 1 := by
      grw [MeasureTheory.measure_mono (t := Set.univ)]
      unfold MeasureTheory.volume
      simp [measure_haar]
      conv =>
        pattern Set.univ
        equals ↑compacts_univ =>
          simp [compacts_univ]

      · rw [MeasureTheory.Measure.haarMeasure_self]
      · simp

    have card_i_le : ENat.card I ≤ (1 : ENNReal) / (MeasureTheory.volume ((Metric.ball (1 : (Matrix.unitaryGroup (Fin n) ℂ)) ((ε / 2)/2)))) := by
      rw [div_eq_mul_inv, mul_comm, ← ENNReal.mul_le_iff_le_inv, mul_comm]
      rw [MeasureTheory.measure_biUnion] at volume_sum
      conv at volume_sum =>
        lhs
        arg 1
        intro i
        rw [translate_ball _ (by linarith)]
      simpa only [Set.image_mul_left, MeasureTheory.measure_preimage_mul,
        ENNReal.tsum_const, ENat.card_coe_set_eq] using volume_sum
      · apply Set.PairwiseDisjoint.countable_of_isOpen (s := fun g => Metric.ball g ((ε / 2)/2))
        · exact disjoint_balls
        · intro i hi
          exact Metric.isOpen_ball
        · intro i hi
          simp [hε]
      · exact disjoint_balls
      · intro i hi
        exact measurableSet_ball
      · apply LT.lt.ne'
        unfold MeasureTheory.volume
        simp [measure_haar]
        apply IsOpen.measure_pos
        exact Metric.isOpen_ball
        simp [hε]
      · unfold MeasureTheory.volume
        simp [measure_haar]
    -- Subgroup.index_le_of_leftCoset_cover_const

    have inter_subset (g) (hg : g ∈ G.carrier): Metric.ball (g : (Matrix.unitaryGroup (Fin n) ℂ)) ε ∩ G.carrier ⊆ (fun x => g * x.val) '' (G' n ε G).carrier := by
      rw [translate_ball]
      intro a ha
      simp only [Set.mem_image]

      have a_mem := Set.mem_of_mem_inter_left ha
      simp only [Set.mem_image] at a_mem
      obtain ⟨x, hx⟩ := a_mem
      have a_mem_g := Set.mem_of_mem_inter_right ha
      simp at a_mem_g
      have g_mul_x := hx.2
      rw [eq_comm] at g_mul_x
      rw [← inv_mul_eq_iff_eq_mul] at g_mul_x
      have x_mem_g : x ∈ G := by
        rw [← g_mul_x]
        apply Subgroup.mul_mem
        · simpa using hg
        · exact a_mem_g

      use ⟨x, x_mem_g⟩
      refine ⟨?_, ?_⟩
      · apply Subgroup.subset_closure
        exact hx.1
      · simp_rw [← g_mul_x]
        simp
      · exact hε

    have card_lt_top : (ENat.card I).toENNReal < ⊤ := by
      grw [card_i_le]
      simp
      unfold MeasureTheory.volume
      simp [measure_haar]
      apply IsOpen.measure_pos
      exact Metric.isOpen_ball
      simp [hε]
    norm_cast at card_lt_top
    rw [lt_top_iff_ne_top] at card_lt_top
    simp at card_lt_top

    have fintype_I : Fintype I := by
      exact Set.Finite.fintype card_lt_top

    have i_mem_G : ∀ i ∈ I, i ∈ G := by
      intro i i_mem
      simp [Maximal] at hI
      have I_prop := hI.1
      simp [-Subtype.forall, I_sets] at I_prop
      apply (I_prop.1 i_mem)


    have cosets_cover : (⋃ i ∈ I.toFinset.attach, (((⟨i.val, i_mem_G i.val (Set.mem_toFinset.mp i.property)⟩ : G) • (((G' n ε G)) : Set G)) : (Set G))) = (Set.univ : Set G) := by
      have balls_inter_cover : G.carrier ⊆ ⋃ g ∈ I, ((Metric.ball g ε) ∩ G.carrier) := by
        intro g hg
        specialize balls_cover hg
        simp only [Set.mem_iUnion] at balls_cover
        obtain ⟨i, i_mem, g_mem_i⟩ := balls_cover
        simp only [Set.mem_iUnion]
        use i
        use i_mem
        exact Set.mem_inter g_mem_i hg


      simp
      ext a
      simp only [Set.mem_univ, iff_true]
      have a_mem_g : a.val ∈ G.carrier := by simp
      specialize balls_inter_cover a_mem_g
      simp only [Set.mem_iUnion] at balls_inter_cover
      obtain ⟨i, i_mem, a_mem_i⟩ := balls_inter_cover
      have i_mem_G : i ∈ G.carrier := by
        simp [Maximal] at hI
        have I_prop := hI.1
        simp [-Subtype.forall, I_sets] at I_prop
        apply (I_prop.1 i_mem)
      specialize inter_subset i i_mem_G
      have a_mem := inter_subset a_mem_i
      simp only [Set.mem_image] at a_mem
      obtain ⟨x, hx, a_eq_mul⟩ := a_mem
      simp only [Set.mem_iUnion]
      have i_mem_finset : i ∈ I.toFinset := by
        exact Set.mem_toFinset.mpr i_mem
      use ⟨i, i_mem_finset⟩
      simp
      rw [Set.mem_smul_set]
      use x
      refine ⟨?_, ?_⟩
      · exact hx
      · rw [Subtype.ext_iff]
        simp [a_eq_mul]

    refine ⟨?_, ?_⟩
    · apply Subgroup.finiteIndex_of_leftCoset_cover_const cosets_cover
    · have I_subset_G : I ⊆ G := by
        simp [Maximal] at hI
        have i_mem := hI.1
        simp [I_sets] at i_mem
        exact i_mem.1


      norm_cast at card_i_le
      grw [Subgroup.index_le_of_leftCoset_cover_const (s := I.toFinset.attach) (g := fun a => (⟨a.val, by (
        have a_mem := a.prop
        have a_mem_i : a.val ∈ I := by
          exact Set.mem_toFinset.mp a_mem
        exact I_subset_G a_mem_i
      )⟩ : G))]

      rw [le_div_iff₀]
      · rw [Finset.card_attach, ← Set.ncard_eq_toFinset_card']
        simp at card_i_le
        rw [← Set.Finite.cast_ncard_eq, ENat.toENNReal_coe, ← ENNReal.toReal_le_toReal] at card_i_le
        simpa using card_i_le
        · apply ENNReal.mul_ne_top
          · simp
          · simp
        · simp
        · exact card_lt_top
      · rw [ENNReal.toReal_pos_iff]
        exact ⟨IsOpen.measure_pos _ Metric.isOpen_ball (by simp [hε]),
          MeasureTheory.measure_lt_top _ _⟩
      · exact cosets_cover

  · intro S S_subset S_chain
    refine ⟨S.sUnion, ?_, ?_⟩
    · simp only [ne_eq, ge_iff_le, Set.mem_setOf_eq,
      Set.sUnion_subset_iff, Set.mem_sUnion, forall_exists_index, and_imp, I_sets]

      refine ⟨?_, ?_⟩
      · intro s hs
        simp [I_sets] at S_subset
        specialize S_subset hs
        simp at S_subset
        exact S_subset.1
      · simp [I_sets] at S_subset
        intro a M M_mem_S a_mem_M b N N_mem_S b_mem_N a_neq_b
        simp [IsChain] at S_chain
        specialize S_chain M_mem_S N_mem_S
        by_cases M_eq_N : M = N
        · rw [M_eq_N] at a_mem_M
          specialize S_subset N_mem_S
          simp at S_subset
          exact S_subset.2 a (by simp) (by simp [a_mem_M]) b (by simp) (by simp [b_mem_N]) (by simp [a_neq_b])
        · specialize S_chain M_eq_N
          match S_chain with
          | .inl h =>
            have a_mem_N := h a_mem_M
            specialize S_subset N_mem_S
            simp at S_subset
            exact S_subset.2 a (by simp) (by simp [a_mem_N]) b (by simp) (by simp [b_mem_N]) (by simp [a_neq_b])
          | .inr h =>
            have b_mem_M := h b_mem_N
            specialize S_subset M_mem_S
            simp at S_subset
            exact S_subset.2 a (by simp) (by simp [a_mem_M]) b (by simp) (by simp [b_mem_M]) (by simp [a_neq_b])


    · intro s hs
      exact Set.subset_sUnion_of_subset S s (fun ⦃a⦄ a ↦ a) hs


attribute [-simp] MeasureTheory.Measure.inv_eq_self

attribute [local implicit_reducible] FreshInnerProduct
end

theorem solution : type_of% @volume_packing_oai := @volume_packing_oai

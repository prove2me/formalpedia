-- Prove2me | solution 1 for lintegral_lowerSemianalytic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:11:31.338658+00:00
-- url     : https://prove2.me/submissions/df1226a1-1ba4-4503-b349-df5b169efdf8

import Definitions.Def_BicausalOT_DescriptiveSetTheory_Capacitability
import Definitions.Def_BicausalOT_DescriptiveSetTheory_LowerSemianalytic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Sub
import Definitions.Def_BicausalOT_DescriptiveSetTheory_KernelIntegral
import Theorems.Thm_P2M_MeasureTheory_AnalyticSet_inter__f59a23aaf291
import Theorems.Thm_MeasureTheory_AnalyticSet_preimage_of_continuous
import Theorems.Thm_ennreal_le_iff_forall_lt_add_inv
import Theorems.Thm_ennreal_iSup_min_natCast
import Theorems.Thm_aemeasurable_of_analytic_sublevels
import Theorems.Thm_MeasureTheory_AnalyticSet_prod_apply
import Theorems.Thm_volume_restrict_epigraph_section
import Theorems.Thm_IsLowerSemianalytic_analyticSet_epigraph
import Theorems.Thm_MeasureTheory_AnalyticSet_kernel_section_gt


set_option autoImplicit false
open Set Topology MeasureTheory ProbabilityTheory Filter
open scoped Classical ENNReal
noncomputable section
variable {X Y : Type*}
  [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
theorem _root_.solution
    {f : X × Y → ℝ≥0∞} (hf : IsLowerSemianalytic (X := X × Y) f)
    {κ : X → Measure Y} (hκ : Measurable κ)
    (hκp : ∀ x, IsProbabilityMeasure (κ x)) :
    IsLowerSemianalytic (fun x => ∫⁻ y, f (x, y) ∂(κ x)) := by
  -- kernel packaging
  set κK : Kernel X Y := ⟨κ, hκ⟩ with hκK
  haveI : IsMarkovKernel κK := ⟨fun a => hκp a⟩
  -- transported epigraph pieces Eₙ ⊆ X × (Y × ℝ)
  set E : ℕ → Set (X × (Y × ℝ)) := fun n =>
    (Homeomorph.prodAssoc X Y ℝ).symm ⁻¹'
      ({pb : (X × Y) × ℝ | f pb.1 ≤ ENNReal.ofReal pb.2}
        ∩ ((univ : Set (X × Y)) ×ˢ Icc (0 : ℝ) n)) with hE
  have hE_analytic : ∀ n, AnalyticSet (E n) := by
    intro n
    refine AnalyticSet.preimage_of_continuous ?_ (Homeomorph.continuous _)
    exact hf.analyticSet_epigraph.inter'
      ((MeasurableSet.univ.prod measurableSet_Icc).analyticSet)
  -- double sections of Eₙ are epigraph slices in ℝ
  have hE_sec : ∀ (n : ℕ) (x : X) (y : Y),
      Prod.mk y ⁻¹' (Prod.mk x ⁻¹' E n)
        = {b : ℝ | f (x, y) ≤ ENNReal.ofReal b} ∩ Icc (0 : ℝ) n := by
    intro n x y
    ext b
    simp only [hE, mem_preimage]
    constructor
    · rintro ⟨h1, -, h2⟩
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, mem_univ _, h2⟩
  -- the Lebesgue factors
  set lam : ℕ → Measure ℝ := fun n => volume.restrict (Icc (0 : ℝ) n) with hlam
  haveI hlam_fin : ∀ n, IsFiniteMeasure (lam n) := fun n => by
    rw [hlam]; infer_instance
  -- truncated integrals
  set a : ℕ → X → ℝ≥0∞ :=
    fun n x => ∫⁻ y, min (f (x, y)) (n : ℝ≥0∞) ∂(κ x) with ha
  have ha_le : ∀ n x, a n x ≤ (n : ℝ≥0∞) := by
    intro n x
    rw [ha]
    refine le_trans (lintegral_mono fun y => min_le_right _ _) ?_
    rw [lintegral_const, measure_univ, mul_one]
  -- sections of f are AEMeasurable
  have hfx_slev : ∀ (x : X) (c : ℝ≥0∞), AnalyticSet {y | f (x, y) < c} := by
    intro x c
    have hset : {y | f (x, y) < c} = Prod.mk x ⁻¹' {p : X × Y | f p < c} := rfl
    rw [hset]
    exact (hf c).preimage_of_continuous
      (Continuous.prodMk continuous_const continuous_id)
  have hfx_ae : ∀ x : X, AEMeasurable (fun y => f (x, y)) (κ x) := fun x =>
    aemeasurable_of_analytic_sublevels (hfx_slev x) (κ x)
  -- key value identity: (κ x ⊗ λₙ)((Eₙ)_x) = n − aₙ x
  have hval : ∀ (n : ℕ) (x : X),
      (κ x).prod (lam n) (Prod.mk x ⁻¹' E n) = (n : ℝ≥0∞) - a n x := by
    intro n x
    have hsec_analytic : AnalyticSet (Prod.mk x ⁻¹' E n) :=
      (hE_analytic n).preimage_of_continuous
        (Continuous.prodMk continuous_const continuous_id)
    rw [hsec_analytic.prod_apply (κ x) (lam n)]
    have hint : ∀ y : Y, (lam n) (Prod.mk y ⁻¹' (Prod.mk x ⁻¹' E n))
        = (n : ℝ≥0∞) - min (f (x, y)) (n : ℝ≥0∞) := by
      intro y
      rw [hE_sec n x y, hlam]
      have h1 : volume.restrict (Icc (0 : ℝ) n)
            ({b : ℝ | f (x, y) ≤ ENNReal.ofReal b} ∩ Icc (0 : ℝ) n)
          = volume.restrict (Icc (0 : ℝ) n)
            {b : ℝ | f (x, y) ≤ ENNReal.ofReal b} := by
        rw [Measure.restrict_apply' measurableSet_Icc,
          Measure.restrict_apply' measurableSet_Icc, inter_assoc, inter_self]
      rw [h1]
      exact volume_restrict_epigraph_section _ n
    rw [lintegral_congr fun y => hint y]
    have hmin_ae : AEMeasurable (fun y => min (f (x, y)) (n : ℝ≥0∞)) (κ x) :=
      (hfx_ae x).min aemeasurable_const
    have hle : (fun y => min (f (x, y)) (n : ℝ≥0∞)) ≤ᵐ[κ x]
        fun _ => (n : ℝ≥0∞) :=
      Filter.Eventually.of_forall fun y => min_le_right _ _
    have hfin : ∫⁻ y, min (f (x, y)) (n : ℝ≥0∞) ∂(κ x) ≠ ∞ :=
      ne_top_of_le_ne_top (by finiteness) (ha_le n x)
    calc ∫⁻ y, ((n : ℝ≥0∞) - min (f (x, y)) (n : ℝ≥0∞)) ∂(κ x)
        = ∫⁻ y, ((fun _ => (n : ℝ≥0∞)) y
            - (fun y => min (f (x, y)) (n : ℝ≥0∞)) y) ∂(κ x) := rfl
      _ = ∫⁻ _, (n : ℝ≥0∞) ∂(κ x)
            - ∫⁻ y, min (f (x, y)) (n : ℝ≥0∞) ∂(κ x) :=
          lintegral_sub' hmin_ae hfin hle
      _ = (n : ℝ≥0∞) - a n x := by
          rw [lintegral_const, measure_univ, mul_one, ha]
  -- parametrized capacitability: superlevels of x ↦ (κ x ⊗ λₙ)((Eₙ)_x)
  have hkey : ∀ (n : ℕ) (c' : ℝ≥0∞),
      AnalyticSet {x | c' < (κ x).prod (lam n) (Prod.mk x ⁻¹' E n)} := by
    intro n c'
    have happ : ∀ x : X, (κK ×ₖ Kernel.const X (lam n)) x = (κ x).prod (lam n) := by
      intro x
      rw [Kernel.prod_apply, Kernel.const_apply]
      rfl
    have h := (hE_analytic n).kernel_section_gt
      (κK ×ₖ Kernel.const X (lam n)) c'
    simpa only [happ] using h
  -- strict sublevels of the truncated integrals are analytic
  have ha_sublevel : ∀ (n : ℕ) (r : ℝ≥0∞), AnalyticSet {x | a n x < r} := by
    intro n r
    rcases le_or_gt r (n : ℝ≥0∞) with hrn | hrn
    · have heq : {x | a n x < r}
          = {x | (n : ℝ≥0∞) - r < (κ x).prod (lam n) (Prod.mk x ⁻¹' E n)} := by
        ext x
        rw [mem_ofPred_eq, mem_ofPred_eq, hval n x]
        constructor
        · intro h
          rw [ENNReal.sub_lt_iff_lt_right
            (ne_top_of_le_ne_top (by finiteness) hrn) hrn]
          calc (n : ℝ≥0∞) = a n x + ((n : ℝ≥0∞) - a n x) :=
                (add_tsub_cancel_of_le (ha_le n x)).symm
            _ < r + ((n : ℝ≥0∞) - a n x) :=
                ENNReal.add_lt_add_right
                  (ne_top_of_le_ne_top (by finiteness) tsub_le_self) h
            _ = ((n : ℝ≥0∞) - a n x) + r := add_comm _ _
        · intro h
          by_contra hra
          rw [not_lt] at hra
          exact absurd h (not_lt.mpr (tsub_le_tsub_left hra _))
      rw [heq]
      exact hkey n _
    · have heq : {x | a n x < r} = univ :=
        eq_univ_of_forall fun x => lt_of_le_of_lt (ha_le n x) hrn
      rw [heq]
      exact MeasurableSet.univ.analyticSet
  -- the integral is the increasing limit of the truncations
  have hsup : ∀ x : X, (∫⁻ y, f (x, y) ∂(κ x)) = ⨆ n : ℕ, a n x := by
    intro x
    calc ∫⁻ y, f (x, y) ∂(κ x)
        = ∫⁻ y, ⨆ n : ℕ, min (f (x, y)) (n : ℝ≥0∞) ∂(κ x) := by
          congr 1
          funext y
          rw [ennreal_iSup_min_natCast]
      _ = ⨆ n : ℕ, a n x := by
          rw [ha]
          exact lintegral_iSup'
            (fun n => (hfx_ae x).min aemeasurable_const)
            (Filter.Eventually.of_forall fun y n m hnm =>
              min_le_min le_rfl (by exact_mod_cast Nat.cast_le.mpr hnm))
  -- countable rational bookkeeping for the supremum
  intro c
  have hgoal : {x | (∫⁻ y, f (x, y) ∂(κ x)) < c}
      = {x | (⨆ n : ℕ, a n x) < c} := by
    ext x
    rw [mem_ofPred_eq, mem_ofPred_eq, hsup x]
  rw [hgoal]
  have hmain : {x | (⨆ n : ℕ, a n x) < c}
      = ⋃ q : ℚ, {x | (Real.toNNReal q : ℝ≥0∞) < c ∧
          ∀ n : ℕ, a n x ≤ (Real.toNNReal q : ℝ≥0∞)} := by
    ext x
    simp only [mem_ofPred_eq, mem_iUnion]
    constructor
    · intro h
      obtain ⟨q, _, h1, h2⟩ := ENNReal.lt_iff_exists_rat_btwn.mp h
      exact ⟨q, h2, fun n =>
        le_of_lt (lt_of_le_of_lt (le_iSup (fun m => a m x) n) h1)⟩
    · rintro ⟨q, hqc, hall⟩
      exact lt_of_le_of_lt (iSup_le fun n => hall n) hqc
  rw [hmain]
  refine AnalyticSet.iUnion fun q => ?_
  by_cases hqc : (Real.toNNReal q : ℝ≥0∞) < c
  · have heq : {x | (Real.toNNReal q : ℝ≥0∞) < c ∧
        ∀ n : ℕ, a n x ≤ (Real.toNNReal q : ℝ≥0∞)}
        = ⋂ (n : ℕ) (k : ℕ),
            {x | a n x < (Real.toNNReal q : ℝ≥0∞) + ((k : ℝ≥0∞) + 1)⁻¹} := by
      ext x
      simp only [mem_ofPred_eq, mem_iInter, hqc, true_and]
      constructor
      · intro h n k
        exact (ennreal_le_iff_forall_lt_add_inv (by finiteness)).mp (h n) k
      · intro h n
        exact (ennreal_le_iff_forall_lt_add_inv (by finiteness)).mpr (h n)
    rw [heq]
    exact AnalyticSet.iInter fun n =>
      AnalyticSet.iInter fun k => ha_sublevel n _
  · have heq : {x | (Real.toNNReal q : ℝ≥0∞) < c ∧
        ∀ n : ℕ, a n x ≤ (Real.toNNReal q : ℝ≥0∞)} = ∅ := by
      ext x
      simp [hqc]
    rw [heq]
    exact analyticSet_empty

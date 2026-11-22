-- Prove2me | solution 1 for formalLearning_analyticSet_nullMeasurableSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:42:41.973547+00:00
-- url     : https://prove2.me/submissions/854839d6-01ba-4f41-bb9c-de45abfd1fac

module
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_ChoquetCapacity
public import Mathlib.MeasureTheory.Measure.Real
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_AnalyticMeasurability
public import Theorems.Thm_MeasureTheory_AnalyticSet_exists_isCompact_measureReal_gt

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set
theorem _root_.solution
    {α : Type*}
    [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α] [PolishSpace α]
    {μ : MeasureTheory.Measure α} [MeasureTheory.IsFiniteMeasure μ]
    {s : Set α} (hs : MeasureTheory.AnalyticSet s) :
    MeasureTheory.NullMeasurableSet s μ := by
  classical
  obtain ⟨t, hst, ht_meas, ht_eq⟩ := MeasureTheory.exists_measurable_superset μ s
  have hzero : μ (t \ s) = 0 := by
    by_contra hne
    have hfin_diff : μ (t \ s) ≠ ⊤ := measure_ne_top μ _
    have hpos : 0 < μ.real (t \ s) := ENNReal.toReal_pos hne hfin_diff
    obtain ⟨K, hKc, hKs, hKapprox⟩ :=
      hs.exists_isCompact_measureReal_gt (μ := μ) (μ.real (t \ s) / 2) (by positivity)
    have hdiff_eq : μ.real (t \ K) = μ.real t - μ.real K :=
      measureReal_sdiff (fun x hx => hst (hKs hx)) hKc.isClosed.measurableSet
    have ht_real : μ.real t = μ.real s := by simp only [Measure.real]; rw [ht_eq]
    have hle : μ.real (t \ s) ≤ μ.real (t \ K) :=
      measureReal_mono (Set.sdiff_subset_sdiff_right hKs)
    -- Combine with hKapprox (μ.real s < μ.real K + μ.real(t \ s)/2) for the contradiction.
    linarith
  have h_ae : s =ᵐ[μ] t :=
    ae_eq_set.mpr ⟨by simp [Set.sdiff_eq_empty.mpr hst], hzero⟩
  exact ht_meas.nullMeasurableSet.congr h_ae.symm

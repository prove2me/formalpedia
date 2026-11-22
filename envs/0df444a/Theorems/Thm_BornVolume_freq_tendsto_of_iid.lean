-- Prove2me | Theorems.Thm_BornVolume_freq_tendsto_of_iid
-- name    : BornVolume.freq_tendsto_of_iid
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:06:56.773605+00:00
-- url     : https://prove2.me/theorems/b433c25d-64a2-468b-b7a5-bde7cc05c764
-- title:
--   Born Volume: freq tendsto of iid
-- statement:
--   **Frequencies of identically distributed trials.** Trials `X n` with common law `μp`, whose
--   indicators of a measurable set `O` are pairwise independent, have empirical frequency of `O`
--   converging almost surely to `(μp O).toReal`. The strong law of large numbers for the indicators.
--
--   Source: https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/BornFrequency.lean#L46-L103
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/BornFrequency.lean#L46-L103

module
public import Definitions.Def_BornVolumeLean_Volume_BornWeight
public import Mathlib.Probability.StrongLaw
public import Mathlib.Probability.IdentDistrib
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Definitions.Def_BornVolumeLean_Volume_BornFrequency
set_option autoImplicit false
@[expose] public section
public section
open MeasureTheory ProbabilityTheory Set Filter Matrix Matrix.UnitaryGroup Projectivization
open scoped ENNReal
open BornVolume

theorem BornVolume.freq_tendsto_of_iid
    {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → S} (hX : ∀ n, Measurable (X n))
    {μp : Measure S} (hlaw : ∀ n, Measure.map (X n) P = μp)
    {O : Set S} (hO : MeasurableSet O)
    (hindep :
      Pairwise
        (Function.onFun (fun f g : Ω → ℝ => IndepFun f g P)
          (fun n => Set.indicator (X n ⁻¹' O) (fun _ => (1 : ℝ))))) :
    ∀ᵐ ω ∂ P,
      Tendsto
        (fun N : ℕ =>
          (∑ i ∈ Finset.range N,
              Set.indicator (X i ⁻¹' O) (fun _ => (1 : ℝ)) ω) / (N : ℝ))
        atTop
        (nhds (μp O).toReal) := by sorry

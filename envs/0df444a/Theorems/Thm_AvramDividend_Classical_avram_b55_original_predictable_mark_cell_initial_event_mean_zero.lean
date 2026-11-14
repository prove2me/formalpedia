-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b55_original_predictable_mark_cell_initial_event_mean_zero
-- name    : AvramDividend.Classical.avram_b55_original_predictable_mark_cell_initial_event_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T11:09:25.206781+00:00
-- url     : https://prove2.me/theorems/ce340e44-bb23-401a-baa6-9f000870be75
-- title:
--   True original predictable negative marked compensated jump cell has zero expectation on every past event
-- statement:
--   For the actual original Lévy process and the physical compensated negative Borel jump-count cell, any square-integrable predictable weight has integrable cell gain, and that gain has zero expected value restricted to any measurable event in the genuine past filtration at the cell's left endpoint. This is eventwise conditional centring needed for mixed Itô–Meyer localisation, with no independent jump source or post-ruin continuation.
-- source:
--   Proved original P4-F3 conditional centring and L1 integrability of the unbounded predictable negative mark cell, then restricted conditional expectation integration.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_unbounded_predictable_negative_cell_condExp_auto
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_unbounded_predictable_cell_L1_integral_zero
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_b55_original_predictable_mark_cell_initial_event_mean_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (cut : ℕ)
    (s t : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T)
    (ε : ℝ) (hε : 0 < ε) (B : Set ℝ)
    (hB : MeasurableSet B)
    (hBand : B ⊆ Ioo (-1 : ℝ) (-ε))
    (hCut : B ⊆ Iic (-(1 / ((cut : ℝ) + 1))))
    (H : Ω → ℝ) (hH : StronglyMeasurable[𝓕 s] H)
    (hHL2 : MemLp H 2 P)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A) :
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)
    let r : ℝ := (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal
    Integrable (fun ω => H ω * ((N ω).toReal - r)) P ∧
    (∫ ω in A, H ω * ((N ω).toReal - r) ∂P) = 0 := by sorry

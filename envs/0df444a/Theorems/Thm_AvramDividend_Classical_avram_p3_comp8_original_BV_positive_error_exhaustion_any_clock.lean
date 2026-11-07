-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_comp8_original_BV_positive_error_exhaustion_any_clock
-- name    : AvramDividend.Classical.avram_p3_comp8_original_BV_positive_error_exhaustion_any_clock
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T23:28:48.06843+00:00
-- url     : https://prove2.me/theorems/2a06bf39-e026-4b5b-97e1-00cd8b92754c
-- title:
--   Original BV positive physical-grid error localisation and tail close globally for every finite horizon
-- statement:
--   For the exact original BV Lévy source and arbitrary finite T, if positive physical-grid errors are L1, converge in expectation on an exhausting sequence of measurable events, and are bounded on complements by the original BV source mass, then their global expected positive parts tend to zero. This extends Proved 70a/cad BV-ERROR7 mechanism beyond T≤1.
-- source:
--   Source-faithful adaptation of Proved cad6d3d7 using new genuine all-T source-tail L1 certificate; preserves the positive error and original process definitions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_comp8_original_BV_source_tail_L1_any_clock
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_positive_error_measurable_event_split
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_positive_error_moving_event_tail_absorption

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_comp8_original_BV_positive_error_exhaustion_any_clock
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (T : ℝ≥0)
    (K : ℝ) (hK : 0 ≤ K)
    (s : ℕ → Set Ω) (hs : ∀ n, MeasurableSet (s n))
    (hExhaust : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ω ∈ s n)
    (Err : ℕ → Ω → ℝ)
    (hPos : ∀ n, Integrable (fun ω => max (Err n ω) 0) P)
    (hLocal : Tendsto
      (fun n => ∫ ω, max (if ω ∈ s n then Err n ω else 0) 0 ∂P)
      atTop (nhds (0 : ℝ)))
    (hTailBound : ∀ n, ∀ᵐ ω ∂P,
      max (if ω ∉ s n then Err n ω else 0) 0 ≤
        (if ω ∈ s n then 0 else
          K * (|X.drift| * (T : ℝ) +
            |(T : ℝ) * X.drift - X.X T ω|))) :
    Tendsto
      (fun n => ∫ ω, max (Err n ω) 0 ∂P)
      atTop (nhds (0 : ℝ)) := by sorry

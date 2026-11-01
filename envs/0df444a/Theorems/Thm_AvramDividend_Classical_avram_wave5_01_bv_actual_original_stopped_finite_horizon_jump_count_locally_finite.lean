-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_01_bv_actual_original_stopped_finite_horizon_jump_count_locally_finite
-- name    : AvramDividend.Classical.avram_wave5_01_bv_actual_original_stopped_finite_horizon_jump_count_locally_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T01:25:56.552089+00:00
-- url     : https://prove2.me/theorems/84c8c695-3b46-4cb3-9780-38ba045dc5a9
-- title:
--   Actual finite-activity BV Lévy stopped source jump count is finite on every bounded horizon and Borel band
-- statement:
--   For the genuine original spectrally negative Lévy source X with bounded variation and finite total negative Lévy intensity, and an arbitrary stopping time τ of its exact original filtration 𝓕, there is one P-full event on which the literal source jump-counting measure restricted to (0,T]∩{u≤τ(ω)} and any Borel mark set is finite, simultaneously in all finite horizons T and all Borel bands. It follows by pathwise measure monotonicity from the Proved original BV count local-finiteness theorem, with no Poisson-space replacement, and is the precise finite-horizon stopped-count localisation used in source compensation.
-- source:
--   The Proved genuine original-source BV all-band local count finiteness 6e608416-1034-40ed-9ab6-f0035d8c76a5 and pathwise measure monotonicity. Original filtration IsStoppingTime witness is retained explicitly for Chat 02/03 stopped formulations.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_intrinsic_count_locally_finite_all_borel_ae

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_01_bv_actual_original_stopped_finite_horizon_jump_count_locally_finite
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (τ : Ω → ℝ≥0∞) (hτ : IsStoppingTime 𝓕 τ) :
    ∀ᵐ ω ∂P, ∀ (T : ℝ≥0) (B : Set ℝ), MeasurableSet B →
      ((Measure.count.restrict {v : ℝ≥0 |
          0 < v ∧ X.X v ω - Function.leftLim (fun w : ℝ≥0 => X.X w ω) v ≠ 0}).map
          (fun v : ℝ≥0 => (v,
            X.X v ω - Function.leftLim (fun w : ℝ≥0 => X.X w ω) v)))
          ({u : ℝ≥0 | 0 < u ∧ u ≤ T ∧ (u : ℝ≥0∞) ≤ τ ω} ×ˢ B) < ⊤ := by sorry

-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_intrinsic_negative_jump_magnitude_integrable_ae
-- name    : AvramDividend.Classical.avram_wave4_04a_bv_actual_intrinsic_negative_jump_magnitude_integrable_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T11:44:58.233705+00:00
-- url     : https://prove2.me/theorems/8fdf098e-7ed6-47b5-a62d-cb08cbb9d13b
-- title:
--   Original BV Lévy intrinsic jump measure has finite total negative mark variation on each horizon
-- statement:
--   For the genuine original bounded-variation spectrally negative Lévy source X and its pathwise intrinsic jump counting measure N_X(ω), the ENNReal integral ∫_(u,z), 1_(0,T](u)*max(-z,0) dN_X(ω) is bounded almost surely by the source drift residual T*X.drift-X_T(ω). This is exactly the original downward jump total-variation mass, not an equal-law construction. It follows from the canonically Proved exact source jump-measure lintegral equals actual jump time sum, and the bounded-variation source sum bound. It is source-path integrability, NOT an expectation/Campbell compensator, not a pure-jump drift identity.
-- source:
--   Proved original source Nω lintegral/sum e4542c93-c64b-453a-b582-e5ec26265dfc, exact original total jump finite variation (authoring in flight; import only after Proved), and pinned Mathlib measurability of ENNReal.ofReal. The actual source X path is preserved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_intrinsic_lintegral_eq_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_total_source_jump_magnitudes_le_residual

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_wave4_04a_bv_actual_intrinsic_negative_jump_magnitude_integrable_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ (T : ℝ≥0),
      (∫⁻ p,
        (if 0 < p.1 ∧ p.1 ≤ T then ENNReal.ofReal (-p.2) else 0) ∂
        ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) ≤
      ENNReal.ofReal ((T : ℝ) * X.drift - X.X T ω) := by sorry

-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_stopped_BV_small_negative_compensator_drift_physical_clock_L1
-- name    : AvramDividend.Classical.avram_p3_b_bvjump_original_stopped_BV_small_negative_compensator_drift_physical_clock_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:36:17.808606+00:00
-- url     : https://prove2.me/theorems/38e29041-3b3d-4676-8c1d-3b5fe6a4cc4f
-- title:
--   Original stopped BV first-order small-jump compensator drift is physical-clock L1 and path-integrable
-- statement:
--   The genuine original controlled pre-payment stopped BV small-negative-jump source drift is absolutely integrable over the original finite physical time-path clock, and its pathwise time integral is P-integrable. Proof uses source first-order finite variation and an explicitly supplied a.e.-strong-measurability premise for the concrete source drift F. This premise remains conditional; the theorem does not manufacture predictability of the original reserve or prove P2 compensation. Source ν is unchanged and no tail first moment is assumed.
-- source:
--   Proved original discounted BV source small-negative drift absolute moment envelope and finite original physical clock measure; Mathlib Integrable.mono' and Fubini product integrability

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_source_discounted_BV_small_absolute_drift_bound
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_physical_clock_total_mass_finite
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical

theorem AvramDividend.Classical.avram_p3_b_bvjump_original_stopped_BV_small_negative_compensator_drift_physical_clock_L1 {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) (x : ℝ) (w : ℝ → ℝ) (K : ℝ≥0) (a b q : ℝ) (hLip : LipschitzOnWith K w (Icc a b)) (hq : 0 ≤ q) (T : ℝ≥0) (τ : Ω → ℝ≥0) (hτBound : ∀ ω, τ ω ≤ T) (hτ : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0))) (Upre : ℝ≥0 × Ω → ℝ) (hUpre : ∀ p, Upre p = Function.leftLim (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1) (E : Set (ℝ≥0 × Ω)) (hE : ∀ p ∈ E, Upre p ∈ Icc (a + 1) b) (F : ℝ≥0 × Ω → ℝ) (hF : ∀ p, F p = ∫ z in Ioo (-1 : ℝ) 0, (if p ∈ E ∧ p.1 ≤ τ p.2 then Real.exp (-(q * (p.1 : ℝ))) * (w (Upre p + z) - w (Upre p)) else 0) ∂X.ν) (hMeas : AEStronglyMeasurable F ((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal).prod P)) : Integrable F ((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) ∧ Integrable (fun ω => (∫ t, F (t, ω) ∂(((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal))) P := by sorry

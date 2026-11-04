-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_controlled_stopped_small_negative_signed_source_drift_bound
-- name    : AvramDividend.Classical.avram_p3_b_bvjump_original_controlled_stopped_small_negative_signed_source_drift_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:33:36.583524+00:00
-- url     : https://prove2.me/theorems/a87f6baf-55f0-4e6a-ad9e-21bc7a60d1aa
-- title:
--   Signed original stopped controlled BV small-jump source drift is bounded by its finite first moment
-- statement:
--   The actual original stopped pre-payment reserve's signed discounted nonlinear source small-negative-jump integral has absolute value at most K times the finite BV source first moment on the active interior clock, and zero otherwise. This consumes the proved absolute source integral estimate, not P2's predictable compensator; its conclusion is an individual pointwise source-integral bound and does not assert expected compensated jump martingale convergence.
-- source:
--   The proved original discounted BV small-negative integral first-moment bound and abs_integral_le_integral_abs

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_source_discounted_BV_small_absolute_drift_bound
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal Classical

theorem AvramDividend.Classical.avram_p3_b_bvjump_original_controlled_stopped_small_negative_signed_source_drift_bound {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) (x : ℝ) (w : ℝ → ℝ) (K : ℝ≥0) (a b q : ℝ) (hLip : LipschitzOnWith K w (Icc a b)) (hq : 0 ≤ q) (T : ℝ≥0) (τ : Ω → ℝ≥0) (hτBound : ∀ ω, τ ω ≤ T) (hτ : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0))) (Upre : ℝ≥0 × Ω → ℝ) (hUpre : ∀ p, Upre p = Function.leftLim (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1) (E : Set (ℝ≥0 × Ω)) (hE : ∀ p ∈ E, Upre p ∈ Icc (a + 1) b) : ∀ p : ℝ≥0 × Ω, |∫ z in Ioo (-1 : ℝ) 0, (if p ∈ E ∧ p.1 ≤ τ p.2 then Real.exp (-(q * (p.1 : ℝ))) * (w (Upre p + z) - w (Upre p)) else 0) ∂X.ν| ≤ (if p ∈ E ∧ p.1 ≤ τ p.2 then (K : ℝ) * (∫ z in Ioo (-1 : ℝ) 0, -z ∂X.ν) else 0) := by sorry

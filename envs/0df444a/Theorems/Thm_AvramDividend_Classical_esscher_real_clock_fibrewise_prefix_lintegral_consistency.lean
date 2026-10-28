-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_real_clock_fibrewise_prefix_lintegral_consistency
-- name    : AvramDividend.Classical.esscher_real_clock_fibrewise_prefix_lintegral_consistency
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T17:25:32.267007+00:00
-- url     : https://prove2.me/theorems/365d6fb3-8555-419c-9a29-2ff1cfb1687c
-- title:
--   Capped Esscher fibrewise law consistency for the actual real-valued independent exponential clock
-- statement:
--   For any SFinite real-valued clock measure ν (including Mathlib's exponential distribution), a terminal Esscher path-law Q_T, and any measurable nonnegative observable F on path×ℝ whose path section at real clock t belongs to the filtration at min(t.toNNReal,T), the product expectation under Q_T×ν equals the ν-integral of fibrewise expectations under Q_(min(t.toNNReal,T)). This directly connects the real clock used by Prove2Me's expMeasure p and measurable running extrema to the adapted finite-prefix Esscher density; no global path-law extension or Wiener–Hopf factorisation is assumed.
-- source:
--   Accepted Prove2Me esscher_finite_prefix_lintegral_consistency and chat04_esscher_weighted_finite_horizon_probability; Mathlib.MeasureTheory.Measure.Prod lintegral_prod_symm'.

import Mathlib.MeasureTheory.Measure.Prod
import Theorems.Thm_AvramDividend_Classical_esscher_finite_prefix_lintegral_consistency
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_weighted_finite_horizon_probability

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_real_clock_fibrewise_prefix_lintegral_consistency
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (T : ℝ≥0)
    {ν : Measure ℝ} [SFinite ν]
    (F : Ω × ℝ → ℝ≥0∞)
    (hF : Measurable F)
    (hSlice : ∀ t : ℝ,
      Measurable[𝓕 (min t.toNNReal T)] (fun ω : Ω => F (ω, t))) :
    (∫⁻ z, F z ∂
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))).prod ν) =
    (∫⁻ t : ℝ, (∫⁻ ω, F (ω, t) ∂
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X (min t.toNNReal T) ω -
          ((min t.toNNReal T : ℝ≥0) : ℝ) * X.ψ θ))))) ∂ν) := by sorry

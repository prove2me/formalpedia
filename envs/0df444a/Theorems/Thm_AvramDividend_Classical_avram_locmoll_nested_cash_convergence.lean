-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_locmoll_nested_cash_convergence
-- name    : AvramDividend.Classical.avram_locmoll_nested_cash_convergence
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T22:02:02.434852+00:00
-- url     : https://prove2.me/theorems/d028baec-012d-5d32-9c59-ce7bd4a4d547
-- title:
--   Monotone closed-clock eligible Stieltjes integrals converge when every eligible time is covered
-- statement:
--   Monotone closed-clock eligible Stieltjes integrals converge when every eligible time is covered
-- source:
--   Exact decomposition of 1956f1aa-dda2-5052-8723-910f7fb63181, Avram Proposition 4(i)

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_locmoll_nested_cash_convergence
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q T : ℝ) (hT : 0 ≤ T) (θ : ℕ → Ω → ℝ≥0)
    (hθle : ∀ k ω, θ k ω ≤ T.toNNReal)
    (hmono : ∀ ω, Monotone (fun k => θ k ω))
    (hcover : ∀ᵐ ω ∂P, ∀ t ∈ paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ∃ k, t ≤ (θ k ω : ℝ)) :
    ∀ᵐ ω ∂P, Tendsto (fun k =>
      ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (θ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) atTop
      (𝓝 (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))) := by sorry

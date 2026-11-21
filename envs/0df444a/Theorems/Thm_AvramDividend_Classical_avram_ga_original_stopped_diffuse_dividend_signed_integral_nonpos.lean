-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_original_stopped_diffuse_dividend_signed_integral_nonpos
-- name    : AvramDividend.Classical.avram_ga_original_stopped_diffuse_dividend_signed_integral_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T20:58:18.60873+00:00
-- url     : https://prove2.me/theorems/bdbafa82-88d2-4701-877b-54da29a29e0b
-- title:
--   True original strictly stopped Stieltjes diffuse dividend correction has nonpositive integral
-- statement:
--   For the original dividendMeasure of any left-continuous admissible dividend strategy, arbitrary singular continuous Stieltjes dividends, positive discount and a smooth auxiliary value function whose gradient is globally at least one, the complete strict-before-stop signed finite-variation dividend cash-plus-gradient integral is nonpositive. This preserves the exact original physical dividend measure and stopping payment convention, and supplies the diffuse part of the smooth right-payment stopped Itô–Stieltjes ledger alongside the separately proved all-atom correction.
-- source:
--   Deterministic sign on the genuine stopped original Stieltjes measure: e^{-qs} is positive and 1-V'(U_s)≤0. No dividend density, countable-jump approximation, or predictable full-cell assumption. Use new Proved global derivative 5caf8432 and original atomic decomposition d19177af in the stochastic source ledger.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_original_stopped_diffuse_dividend_signed_integral_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (V : ℝ → ℝ) (hSlope : ∀ y : ℝ, 1 ≤ deriv V y)
    (ω : Ω) (ρ : ℝ≥0)
    (hI : IntegrableOn (fun s : ℝ =>
      Real.exp (-(q * s)) *
        (1 - deriv V (riskProcess X x D (Real.toNNReal s) ω)))
      (Iio (ρ : ℝ)) (dividendMeasure D ω)) :
    (∫ s in Iio (ρ : ℝ),
      Real.exp (-(q * s)) *
        (1 - deriv V (riskProcess X x D (Real.toNNReal s) ω))
      ∂(dividendMeasure D ω)) ≤ 0 := by sorry

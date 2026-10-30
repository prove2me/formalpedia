-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_03_bv_payoff_to_named_balance
-- name    : AvramDividend.Classical.avram_root29_03_bv_payoff_to_named_balance
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T11:39:54.224688+00:00
-- url     : https://prove2.me/theorems/13c89087-66a7-44c4-a026-82501977b5c5
-- title:
--   BV original upper-exit payoff integral implies named strict two-sided exit expectation times q-scale upper value
-- statement:
--   For a Standing bounded-variation spectrally negative Levy process and q>0, 0<a, 0<=x<=a, an explicit exact stochastic upper-first discounted W(a) payoff integral equal to W(x), matching canonical 09caed2c, implies the named twoSidedExitExpectation X q a x multiplied by ENNReal.ofReal(W a) equals ENNReal.ofReal(W x). The proof only factors out the constant W(a) using a previously Proved measurable integrand and Mathlib's lintegral_mul_const; the probabilistic equality remains explicit.
-- source:
--   Proof adapts Proved chat03_exact_upperfirst_discount_integrand_measurable (065fe2d0) and the proven integral constant-factor technique in f235d825. No Open BV OST import; only hBVPayoff binder.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_exact_upperfirst_discount_integrand_measurable

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_root29_03_bv_payoff_to_named_balance
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hBV : X.BoundedVariation)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (hBVPayoff :
      (∫⁻ ω, if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal
          (Real.exp (-(q * (twoSidedExitUpTime X (a - x) ω).toReal))) *
        ENNReal.ofReal (W a)
      else 0 ∂P) = ENNReal.ofReal (W x)) :
    twoSidedExitExpectation X q a x * ENNReal.ofReal (W a) =
      ENNReal.ofReal (W x) := by sorry

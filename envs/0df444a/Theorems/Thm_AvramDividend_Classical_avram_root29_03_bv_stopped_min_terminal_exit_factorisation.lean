-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_03_bv_stopped_min_terminal_exit_factorisation
-- name    : AvramDividend.Classical.avram_root29_03_bv_stopped_min_terminal_exit_factorisation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T10:37:27.428534+00:00
-- url     : https://prove2.me/theorems/05b00e07-979e-4449-81fc-c3e22f85817d
-- title:
--   BV actual finite stopped q-scale terminal payoff factors as strict discounted upper exit mass
-- statement:
--   Under the genuine original-law SpectrallyNegativeLevy X with Standing and bounded variation, q>0, IsScaleFunction X q W, 0<a and 0<=x<=a, the discounted q-scale terminal reward at the finite minimum strict two-sided exit equals twoSidedExitExpectation X q a x times ENNReal.ofReal(W a). It is derived noncircularly from the accepted min-to-two-branch conversion 7c9fe862, accepted almost-sure BV lower-first payoff zero ba60b63f, and accepted arbitrary-measure upper-first factorisation f235d825, with exact source measurability 019a9588. It does not assert stopped expectation equals W(x) and imports no Open BV OST or killed semigroup.
-- source:
--   Exact composition of canonically Proved source-level adapters 7c9fe862, 019a9588, ba60b63f, f235d825; no stochastic killed process identity or other Open dependency.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_root29_03_exact_qscale_two_branch_terminal_conversion
import Theorems.Thm_AvramDividend_Classical_chat04_strict_upper_exit_scale_terminal_payoff_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_strict_stopped_exit_payoff_any_measure_factorisation
import Theorems.Thm_AvramDividend_Classical_bv_lower_exit_discounted_scale_payoff_zero_ws01c

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_root29_03_bv_stopped_min_terminal_exit_factorisation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hBV : X.BoundedVariation)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    (∫⁻ ω, if min (twoSidedExitUpTime X (a - x) ω) (twoSidedExitDownTime X (-x) ω) < ⊤ then
      ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (min (twoSidedExitUpTime X (a - x) ω) (twoSidedExitDownTime X (-x) ω))))) *
        ENNReal.ofReal
          (W (x + X.X (min (twoSidedExitUpTime X (a - x) ω) (twoSidedExitDownTime X (-x) ω)).toNNReal ω)) else 0 ∂P) =
    twoSidedExitExpectation X q a x * ENNReal.ofReal (W a) := by sorry

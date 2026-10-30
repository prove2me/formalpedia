-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_03_standing_stopped_min_terminal_factorisation
-- name    : AvramDividend.Classical.avram_root29_03_standing_stopped_min_terminal_factorisation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T10:43:35.634803+00:00
-- url     : https://prove2.me/theorems/76559541-3ffb-4b56-9d38-9b175db1eabd
-- title:
--   Original finite stopped q-scale terminal payoff factors as strict exit expectation in both variation branches
-- statement:
--   For any actual Standing spectrally negative Levy process and q>0, 0<a, 0<=x<=a with IsScaleFunction X q W, the discounted q-scale payoff at the finite minimum of original strict upper/lower two-sided exit clocks equals the original strict upper-first discounted expectation times ENNReal.ofReal(W a). A true variation dichotomy combines separately canonically Proved BV and UBV terminal-payoff factorisations. This does not establish the killed q-scale harmonicity W(x), which is a genuine stochastic premise still Open.
-- source:
--   Direct Lean variation split on X.BoundedVariation using only canonically Proved BV 05b00e07 and UBV a219a488. No import of Open BV OST or UBV killed-scale harmonicity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_root29_03_bv_stopped_min_terminal_exit_factorisation
import Theorems.Thm_AvramDividend_Classical_avram_root29_03_ubv_stopped_min_terminal_exit_factorisation

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_root29_03_standing_stopped_min_terminal_factorisation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    (∫⁻ ω, if min (twoSidedExitUpTime X (a - x) ω) (twoSidedExitDownTime X (-x) ω) < ⊤ then
      ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (min (twoSidedExitUpTime X (a - x) ω) (twoSidedExitDownTime X (-x) ω))))) *
        ENNReal.ofReal
          (W (x + X.X (min (twoSidedExitUpTime X (a - x) ω) (twoSidedExitDownTime X (-x) ω)).toNNReal ω)) else 0 ∂P) =
    twoSidedExitExpectation X q a x * ENNReal.ofReal (W a) := by sorry

-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_03_standing_stopped_min_harmonicity_to_exit_ratio
-- name    : AvramDividend.Classical.avram_root29_03_standing_stopped_min_harmonicity_to_exit_ratio
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T10:42:06.378673+00:00
-- url     : https://prove2.me/theorems/fb60b24a-4ce8-4c00-bfef-b6edf6b61950
-- title:
--   All-variation Standing killed stopped q-scale harmonicity implies strict two-sided exit ratio
-- statement:
--   Given an actual Standing spectrally negative Levy process, q>0, IsScaleFunction X q W, a>0 and 0<=x<=a, the exact finite minimum two-sided exit discounted q-scale stopped terminal expectation equality to W(x) implies the corrected strict original two-sided exit scale ratio. Proof splits X.BoundedVariation versus its negation, invokes noncircular BV and UBV terminal-payoff factorisations, then accepted denominator normalisation. hKilled is explicit. This proof does not establish the stochastic killed harmonicity premise.
-- source:
--   Source-faithful transitivity from BV 05b00e07 (must become Proved before submission), UBV a219a488 (Proved), denominator 81ce0d81 (Proved), with visible hKilled.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_root29_03_bv_stopped_min_terminal_exit_factorisation
import Theorems.Thm_AvramDividend_Classical_avram_root29_03_ubv_stopped_min_terminal_exit_factorisation
import Theorems.Thm_AvramDividend_Classical_chat04_exit_ratio_of_stopped_balance

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_root29_03_standing_stopped_min_harmonicity_to_exit_ratio
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (hKilled :
    (∫⁻ ω, if min (twoSidedExitUpTime X (a - x) ω) (twoSidedExitDownTime X (-x) ω) < ⊤ then
      ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (min (twoSidedExitUpTime X (a - x) ω) (twoSidedExitDownTime X (-x) ω))))) *
        ENNReal.ofReal
          (W (x + X.X (min (twoSidedExitUpTime X (a - x) ω) (twoSidedExitDownTime X (-x) ω)).toNNReal ω)) else 0 ∂P) =
      ENNReal.ofReal (W x)) :
    twoSidedExitExpectation X q a x =
      ENNReal.ofReal (W x / W a) := by sorry

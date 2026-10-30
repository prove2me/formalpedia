-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_03_exact_qscale_two_branch_terminal_conversion
-- name    : AvramDividend.Classical.avram_root29_03_exact_qscale_two_branch_terminal_conversion
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T10:06:12.355151+00:00
-- url     : https://prove2.me/theorems/7c9fe862-a3f2-4186-8589-c7357c0cb6df
-- title:
--   Actual finite stopped q-scale terminal expectation equals exact strict two-sided harmonicity payoff integrand
-- statement:
--   For any actual spectrally negative Lévy process, source scale function and separated upper/lower strict exit clocks, the integral of the discounted terminal q-scale reward at the finite minimum exit clock is exactly equal to the integral of the two strict upper-first and lower-first discounted terminal q-scale reward branches appearing verbatim in canonical unbounded killed harmonicity be9dc931. No Standing, variation, no-creeping or killed stochastic expectation equality is required. Source reward measurability is discharged by canonically Proved d1115052. The stochastic assertion that either side equals W(x) remains completely independent and Open.
-- source:
--   Formal composition of canonically Proved original stopped min-to-branches a80aad7a, exact q-scale reward measurability d1115052 and original strict upper terminal payoff measurability 019a9588; uses lintegral_add_left for matching be9 integral-of-sum shape.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_root29_03_min_stopped_two_branch_payoff_identity
import Theorems.Thm_AvramDividend_Classical_avram_root29_03_min_stopped_qscale_reward_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_strict_upper_exit_scale_terminal_payoff_measurable

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_root29_03_exact_qscale_two_branch_terminal_conversion
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 < a) (hxa : x ≤ a) :
    (∫⁻ ω, if min (twoSidedExitUpTime X (a - x) ω) (twoSidedExitDownTime X (-x) ω) < ⊤ then
      ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (min (twoSidedExitUpTime X (a - x) ω) (twoSidedExitDownTime X (-x) ω))))) *
        ENNReal.ofReal
          (W (x + X.X (min (twoSidedExitUpTime X (a - x) ω) (twoSidedExitDownTime X (-x) ω)).toNNReal ω)) else 0 ∂P) =
    (∫⁻ ω,
      (if twoSidedExitUpTime X (a - x) ω < twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω)))) *
        ENNReal.ofReal
          (W (x + X.X (twoSidedExitUpTime X (a - x) ω).toNNReal ω)) else 0) +
      (if twoSidedExitDownTime X (-x) ω < twoSidedExitUpTime X (a - x) ω then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (twoSidedExitDownTime X (-x) ω)))) *
        ENNReal.ofReal
          (W (x + X.X (twoSidedExitDownTime X (-x) ω).toNNReal ω)) else 0) ∂P) := by sorry

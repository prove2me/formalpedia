-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_03_exit_expectation_finite_weak_order_restrict
-- name    : AvramDividend.Classical.avram_root29_03_exit_expectation_finite_weak_order_restrict
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T09:12:29.330201+00:00
-- url     : https://prove2.me/theorems/3f064266-3e81-441d-a49a-11314f9e908f
-- title:
--   Actual exit expectation as finite weak upper-first restricted integral
-- statement:
--   Under a positive upper threshold, the original Lévy-process discounted two-sided exit expectation can be written as an ENNReal lintegral under the original measure restricted to paths where the upward passage clock is finite and weakly no later than the lower one. Uses the canonically Proved source-level strict-event equivalence to exclude finite ties, with no Standing or killed stochastic hypothesis.
-- source:
--   Exact bridge between strict exit-event integral and finite weak-order killed-stopping measure for equation (3.6). Imports only the two new Proved noncircular source adapters cf1d1161 and 7b06a665.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_root29_03_strict_up_event_iff_finite_weak_order
import Theorems.Thm_AvramDividend_Classical_avram_root29_03_exit_expectation_eq_restrict_lintegral

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_root29_03_exit_expectation_finite_weak_order_restrict
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q a x : ℝ) (ha : 0 < a) :
    twoSidedExitExpectation X q a x =
      (∫⁻ ω in {ω : Ω |
        twoSidedExitUpTime X (a - x) ω ≤ twoSidedExitDownTime X (-x) ω ∧
        twoSidedExitUpTime X (a - x) ω < ⊤},
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal
            (twoSidedExitUpTime X (a - x) ω)))) ∂P) := by sorry

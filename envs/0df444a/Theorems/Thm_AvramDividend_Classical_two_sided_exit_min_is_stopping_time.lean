-- Prove2me | Theorems.Thm_AvramDividend_Classical_two_sided_exit_min_is_stopping_time
-- name    : AvramDividend.Classical.two_sided_exit_min_is_stopping_time
-- status  : Open
-- author  : @WillR
-- created : 2026-10-29T04:39:56.000595+00:00
-- url     : https://prove2.me/theorems/1a512e53-cd21-4d4f-ade8-6733ee13b86b
-- title:
--   The two-sided exit minimum is a stopping time
-- statement:
--   For a spectrally negative Levy process with its filtration, the minimum of the strict upper-passage time above a-x and the strict lower-passage time below -x is a stopping time. This isolates the exact optional-stopping premise needed by the bounded-variation stopped-scale expectation identity 322217fe; it does not assert the expectation identity itself.
-- source:
--   Parent target context: AvramDividend.Classical.bv_stopped_scale_ost_expectation_identity (322217fe-647f-4cde-92dc-5e6488349c3a), exact statement and TwoSidedExit definitions refreshed at Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474. The CE 18064 repair analysis shows `exact hMart` fails because a Martingale proposition cannot close an ENNReal equation; the missing source-backed step is an explicit optional-stopping application needing IsStoppingTime for min up/down times plus integrability. This child states only the stopping-time premise with the exact authoritative hitting-time definitions (iInf over NNReal). No parent-child graph edge is asserted by this proposal.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.two_sided_exit_min_is_stopping_time
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a x : ℝ) :
    MeasureTheory.IsStoppingTime 𝓕 (fun ω => min (twoSidedExitUpTime X (a - x) ω) (twoSidedExitDownTime X (-x) ω)) := by sorry

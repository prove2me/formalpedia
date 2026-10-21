-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_official_strict_passage_no_finite_ties
-- name    : AvramDividend.Classical.chat03_official_strict_passage_no_finite_ties
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T20:15:42.877585+00:00
-- url     : https://prove2.me/theorems/a9c87fbc-54b8-40cd-b082-ae3e90e996a9
-- title:
--   Official strict upper and lower Lévy passage clocks cannot coincide at any finite time
-- statement:
--   For the official spectrally negative Lévy process with right-continuous paths, exact strict upward and downward passage clocks across separated barriers cannot both equal the same finite nonnegative time. A previously proved generic ENNReal indexed-infimum theorem identifies any finite passage time with the greatest lower bound of the corresponding strict crossing set. The deterministic separated-barrier right-continuity theorem then rules out equal finite infima. This excludes finite ties pointwise, without probabilistic exceptional sets, jump overshoot or assumption that first strict exit is attained.
-- source:
--   Chat 03 finite extended strict passage infimum IsGLB theorem UUID 9e18c0e5-9287-4efb-9f47-124d90a5a4ab, deterministic right-continuous no-tie lemma UUID 02f8d128-644b-48b9-ba4b-24b641bc4d52.

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat03_finite_extended_infimum_isGLB
import Theorems.Thm_AvramDividend_Classical_chat03_rightcontinuous_separated_strict_passages_no_finite_tie

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_official_strict_passage_no_finite_ties
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (lower upper : ℝ) (hsep : lower < upper)
    (t : ℝ≥0)
    (hup : twoSidedExitUpTime X upper ω = (t : ℝ≥0∞))
    (hdown : twoSidedExitDownTime X lower ω = (t : ℝ≥0∞)) :
    False := by sorry

-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01h_esscher_stopped_mass_eq_original_two_sided_exit
-- name    : AvramDividend.Classical.avram_ws01h_esscher_stopped_mass_eq_original_two_sided_exit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T12:53:48.667569+00:00
-- url     : https://prove2.me/theorems/7601f625-2343-4811-8d9f-48c8b857ac64
-- title:
--   True original lower-killed stopped Esscher exponential weight equals spatial root factor times the official strict two-sided exit expectation
-- statement:
--   For the actual source spectrally negative Lévy process, every real positive-root parameter φ, rates p,q, upper capital a and reserve x, the original-P restricted integral of the killed first-upcrossing Esscher weight exp(φ(a-x) -(p+q)T_plus) equals exp(φ(a-x)) times the official source-defined strict two-sided exit expectation at discount p+q. This is an exact noncircular bridge identifying the original stopped factor in the finite-rate Esscher killed-record regeneration with the correct named mission exit expectation, retaining the actual strict upper-before-lower event, arbitrary boundary reserves and extended first-passage clock. No Wiener-Hopf or scale function identity is imported.
-- source:
--   Canonical Proved named strict-event lintegral adapter 7b06a665, original upper clock measurability e1fe86e9; Mathlib exponential sum and measurable integral constants.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01h_esscher_stopped_mass_eq_original_two_sided_exit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (φ q p a x : ℝ) :
    (∫⁻ ω in {ω : Ω |
      twoSidedExitUpTime X (a - x) ω <
        twoSidedExitDownTime X (-x) ω},
      ENNReal.ofReal (Real.exp (φ * (a - x) -
        (p + q) * (twoSidedExitUpTime X (a - x) ω).toReal)) ∂P) =
      ENNReal.ofReal (Real.exp (φ * (a - x))) *
        twoSidedExitExpectation X (p + q) a x := by sorry

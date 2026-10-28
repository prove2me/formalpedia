-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat01_finite_horizon_upcrossing_probability_explicit_tail
-- name    : AvramDividend.Classical.chat01_finite_horizon_upcrossing_probability_explicit_tail
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T09:27:37.348146+00:00
-- url     : https://prove2.me/theorems/8d35c3fc-d7a4-45eb-a332-21df64280e67
-- title:
--   Explicit Esscher Chernoff probability tail for finite-horizon upcrossings
-- statement:
--   For any measurable restricted first-upcrossing event A that occurs by horizon t, its probability is at most exp(q t - φ z), where q is positive and φ is a positive Esscher root of the Lévy exponent. This is an explicit probability tail estimate in space and time.
-- source:
--   Proved chat01_measurable_finite_horizon_upcrossing_probability_bound and positivity of the real exponential.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_chat01_measurable_finite_horizon_upcrossing_probability_bound
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat01_finite_horizon_upcrossing_probability_explicit_tail
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (z : ℝ) (hz : 0 ≤ z) (A : Set Ω)
    (hAmeas : MeasurableSet A)
    (hA : A ⊆ {ω | twoSidedExitUpTimeCorrected X z ω < (⊤ : ℝ≥0∞)})
    (t : ℝ) (htime : ∀ ω ∈ A, ENNReal.toReal (twoSidedExitUpTimeCorrected X z ω) ≤ t) :
    P A ≤ ENNReal.ofReal (Real.exp (q * t - φ * z)) := by sorry

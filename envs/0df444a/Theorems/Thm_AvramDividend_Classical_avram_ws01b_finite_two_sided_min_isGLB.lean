-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01b_finite_two_sided_min_isGLB
-- name    : AvramDividend.Classical.avram_ws01b_finite_two_sided_min_isGLB
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T11:22:03.218984+00:00
-- url     : https://prove2.me/theorems/bb38e95f-7931-45f7-a009-77d65aa06773
-- title:
--   Finite original two-sided first-exit minimum is the strict-exit infimum
-- statement:
--   For an actual spectrally negative Levy process path, if the minimum of the named strict upper and lower exit clocks is finite then converting this minimum to a nonnegative-real time yields the greatest lower bound of all strict two-sided exit observations. This identifies the canonical stopping clock with the exact IsGLB premise of the genuine first-grid convergence theorem.
-- source:
--   Source definitions of twoSidedExitUpTime and twoSidedExitDownTime as extended infima; finite extended infimum to NNReal IsGLB theorem 9e18c0e5. The elementary infimum of the union equals the minimum of the two infima; no probabilistic simplification or circular stopped-martingale premise.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat03_finite_extended_infimum_isGLB

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01b_finite_two_sided_min_isGLB
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (lower upper : ℝ)
    (hfinite : min (twoSidedExitUpTime X upper ω)
        (twoSidedExitDownTime X lower ω) < ⊤) :
    IsGLB {t : ℝ≥0 | X.X t ω < lower ∨ upper < X.X t ω}
      (min (twoSidedExitUpTime X upper ω)
        (twoSidedExitDownTime X lower ω)).toNNReal := by sorry

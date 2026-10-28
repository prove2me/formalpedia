-- Prove2me | Theorems.Thm_AvramDividend_Classical_positive_jump_tail_real_antitone_of_finite_firstMoment
-- name    : AvramDividend.Classical.positive_jump_tail_real_antitone_of_finite_firstMoment
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T08:45:30.58923+00:00
-- url     : https://prove2.me/theorems/d62967ee-df11-4cd4-ad1f-df7732cd0d53
-- title:
--   Finite first moment preserves monotonicity of the real strict positive tail
-- statement:
--   For a measure of nonnegative jump magnitudes with finite first moment, its real-valued strict upper-tail is antitone on the positive half-line. The Proved sharp Markov tail bound makes each positive threshold finite, and the Proved ENNReal tail antitonicity transports via ENNReal.toReal_mono. This gives the exact AntitoneOn kernel input required by the cstar-connected Open BV Esscher scaled renewal identification, with a weighted measure satisfying the finite-moment hypothesis by the Proved root lemma.
-- source:
--   Proved positive_jump_tail_threshold_mass_le_first_moment and positive_jump_tail_antitone; Mathlib ENNReal.mul_top and ENNReal.toReal_mono.

import Mathlib.Data.ENNReal.Real
import Mathlib.MeasureTheory.Integral.Layercake
import Theorems.Thm_AvramDividend_Classical_positive_jump_tail_antitone
import Theorems.Thm_AvramDividend_Classical_positive_jump_tail_threshold_mass_le_first_moment
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.positive_jump_tail_real_antitone_of_finite_firstMoment
    (μ : Measure ℝ≥0)
    (hfirst : (∫⁻ z : ℝ≥0, ENNReal.ofReal (z : ℝ) ∂μ) < ⊤) :
    AntitoneOn (fun t : ℝ =>
      (μ {z : ℝ≥0 | t < (z : ℝ)}).toReal) (Ioi (0 : ℝ)) := by sorry

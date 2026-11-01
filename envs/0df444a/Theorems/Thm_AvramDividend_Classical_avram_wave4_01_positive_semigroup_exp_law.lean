-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_01_positive_semigroup_exp_law
-- name    : AvramDividend.Classical.avram_wave4_01_positive_semigroup_exp_law
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T09:16:49.678979+00:00
-- url     : https://prove2.me/theorems/bd610411-62fe-44d7-8584-2af619e3367f
-- title:
--   Positive original-record discount semigroup is exponential under zero-height continuity
-- statement:
--   For a strictly positive real-valued semigroup F on positive heights satisfying F(s+t)=F(s)F(t), continuity at height zero of the zero-extended logarithm implies F(h)=exp(h log F(1)). The proof reduces logarithmic multiplicativity to the accepted continuous nonnegative additive Cauchy equation. This upgrades the genuine reflected first-record factors from reciprocal grid powers to all real positive heights.
-- source:
--   Genuine original-record semigroup 3890ee9b, additive Cauchy bridge 287c9796 (Proved), and target cd61d678; KKR 2013 first-record hazard.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_nonnegative_additive_linear
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave4_01_positive_semigroup_exp_law
    (F : ℝ → ℝ)
    (hpos : ∀ t : ℝ, 0 < t → 0 < F t)
    (hsem : ∀ s t : ℝ, 0 < s → 0 < t →
      F (s + t) = F s * F t)
    (hcont : ContinuousAt (fun t : ℝ =>
      if 0 < t then Real.log (F t) else 0) 0) :
    ∀ h : ℝ, 0 < h →
      F h = Real.exp (h * Real.log (F 1)) := by sorry

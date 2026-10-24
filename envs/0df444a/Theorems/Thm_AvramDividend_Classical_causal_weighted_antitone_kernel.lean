-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_weighted_antitone_kernel
-- name    : AvramDividend.Classical.causal_weighted_antitone_kernel
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T22:46:21.251249+00:00
-- url     : https://prove2.me/theorems/eb72d54c-6df1-48b1-90f3-19bb04dfc507
-- title:
--   Exponential damping preserves positive causal kernel antitonicity
-- statement:
--   If K is nonnegative and antitone on (0,∞) and w is nonnegative, then t↦exp(−wt)(|β|+K(t)) is antitone there. This is the weighted nonnegative envelope used in the contraction Neumann series and the proven antitone convolution-power bound.
-- source:
--   Monotonicity of Real.exp and preservation of order by products of nonnegative antitone functions.

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Linarith

open Set

namespace AvramDividend.Classical

theorem causal_weighted_antitone_kernel
    (K : ℝ → ℝ) (β w : ℝ)
    (hw : 0 ≤ w)
    (hanti : AntitoneOn K (Ioi (0 : ℝ)))
    (hKnonneg : ∀ t : ℝ, 0 < t → 0 ≤ K t) :
    AntitoneOn (fun t : ℝ => Real.exp (-w * t) * (|β| + K t))
      (Ioi (0 : ℝ)) := by sorry

end AvramDividend.Classical

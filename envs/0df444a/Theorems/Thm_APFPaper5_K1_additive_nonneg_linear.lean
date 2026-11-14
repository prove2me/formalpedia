-- Prove2me | Theorems.Thm_APFPaper5_K1_additive_nonneg_linear
-- name    : APFPaper5.K1.additive_nonneg_linear
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:25:03.963061+00:00
-- url     : https://prove2.me/theorems/d226a44b-b822-4810-bc59-91e546607652
-- title:
--   Nonnegative additive functions are linear on the nonnegative reals
-- statement:
--   Let f be a real-valued function on the reals. Assume hadd: f(s+t)=f(s)+f(t) whenever s and t are nonnegative, and hnn: f(s) is nonnegative whenever s is nonnegative. Then f(s)=s f(1) for every nonnegative s. The sign condition supplies monotonicity on that domain, allowing the Archimedean argument. No normalization of f(1), statement about negative arguments, or physical additivity law is asserted. This is a conditional theorem of ordinary real analysis.
-- source:
--   Sib v15 frozen source: Theorems/Thm_APFPaper5_K1_additive_nonneg_linear.lean:22; C:/Users/brook/Dev/apf-codebase/apf/standalone/L_Cauchy_uniqueness.py, 1-109

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option autoImplicit false
namespace APFPaper5.K1
end APFPaper5.K1
open APFPaper5.K1

theorem APFPaper5.K1.additive_nonneg_linear (f : ℝ → ℝ)
    (hadd : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → f (s + t) = f s + f t)
    (hnn : ∀ s : ℝ, 0 ≤ s → 0 ≤ f s) :
    ∀ s : ℝ, 0 ≤ s → f s = s * f 1 := by sorry

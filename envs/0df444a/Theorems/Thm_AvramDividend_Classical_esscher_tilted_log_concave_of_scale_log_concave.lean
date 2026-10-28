-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_tilted_log_concave_of_scale_log_concave
-- name    : AvramDividend.Classical.esscher_tilted_log_concave_of_scale_log_concave
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T13:27:10.440997+00:00
-- url     : https://prove2.me/theorems/146db6a8-4fa8-4e75-8077-2dc797ba63f3
-- title:
--   Esscher exponential tilting preserves logarithmic concavity of the scale function
-- statement:
--   Suppose W is strictly positive on the positive half-line, V(x)=exp(-φx)W(x), and log W is concave there. Then log V is concave there as well, because Esscher tilting adds an affine term to the logarithm. This is the exact analytic transfer needed to isolate the probabilistic log-concavity step from the Esscher algebra.
-- source:
--   Real.log_mul, Real.log_exp and ConcaveOn.add from Mathlib.Analysis.Convex.Function and Mathlib.Analysis.SpecialFunctions.Log.Basic.

import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Ring
open Set

theorem AvramDividend.Classical.esscher_tilted_log_concave_of_scale_log_concave
    (φ : ℝ) (W V : ℝ → ℝ)
    (hWpos : ∀ x : ℝ, 0 < x → 0 < W x)
    (hV : ∀ x : ℝ, 0 < x → V x = Real.exp (-(φ * x)) * W x)
    (hWconcave : ConcaveOn ℝ (Set.Ioi (0 : ℝ))
      (fun x : ℝ => Real.log (W x))) :
    ConcaveOn ℝ (Set.Ioi (0 : ℝ)) (fun x : ℝ => Real.log (V x)) := by sorry

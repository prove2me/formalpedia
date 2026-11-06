-- Prove2me | Theorems.Thm_BianchiIX_reciprocal_radial_bounds
-- name    : BianchiIX.reciprocal_radial_bounds
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T06:55:27.518261+00:00
-- url     : https://prove2.me/theorems/54382ca2-c158-45e1-9805-066d6432fde3
-- title:
--   Positive phase slopes give quantitative decreasing reciprocal radii
-- statement:
--   Let $r>0$, $M\geq0$, and let $f$ be differentiable at $x$.
--   Suppose $r/16\leq f(x)\leq Br$ and $1/8\leq f'(x)\leq M$.
--   Then $h(y)=2/f(y)$ is differentiable at $x$ and
--   $$\frac2{Br}\leq h(x)\leq\frac{32}r,\qquad
--   \frac1{4B^2r^2}\leq-h'(x)\leq\frac{512M}{r^2}.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/ReciprocalRadialBounds.lean#L11-L46

import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX

theorem BianchiIX.reciprocal_radial_bounds {f : ℝ → ℝ} {x r B M : ℝ}
    (hr : 0 < r) (hM : 0 ≤ M) (hf : DifferentiableAt ℝ f x)
    (hlo : r / 16 ≤ f x) (hhi : f x ≤ B * r)
    (hdlo : 1 / 8 ≤ deriv f x) (hdhi : deriv f x ≤ M) :
    DifferentiableAt ℝ (fun y => 2 / f y) x ∧
      2 / (B * r) ≤ 2 / f x ∧ 2 / f x ≤ 32 / r ∧
      1 / (4 * B ^ 2 * r ^ 2) ≤ -deriv (fun y => 2 / f y) x ∧
      -deriv (fun y => 2 / f y) x ≤ 512 * M / r ^ 2 := by sorry

-- Prove2me | Theorems.Thm_BianchiIX_multiplier_radial_derivative
-- name    : BianchiIX.multiplier_radial_derivative
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T07:03:15.485917+00:00
-- url     : https://prove2.me/theorems/b2ff34d3-a45c-4dff-b94d-98141bcfa6b7
-- title:
--   Positive multipliers preserve amplitude weights in ordinary derivatives
-- statement:
--   Let $u,m:\mathbb R\to\mathbb R$ be differentiable at $x$,
--   $u(x)\geq0$, $m(x)>0$, and suppose $f=um$ near $x$. If
--   $|u'(x)|\leq a u(x)$ and $|(\log m)'(x)|\leq b$, then $f$ is
--   differentiable at $x$, $f(x)\geq0$, and
--   $$f'(x)=m(x)\bigl(u'(x)+u(x)(\log m)'(x)\bigr),\qquad
--   |f'(x)|\leq f(x)(a+b).$$
--   If $u(x)=0$, both $f(x)$ and $f'(x)$ vanish.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/MultiplierRadialDerivative.lean#L15-L44

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX
open Filter
open scoped Topology

theorem BianchiIX.multiplier_radial_derivative {u m f : ℝ → ℝ} {x a b : ℝ}
    (hu : DifferentiableAt ℝ u x) (hm : DifferentiableAt ℝ m x)
    (hu0 : 0 ≤ u x) (hm0 : 0 < m x)
    (heq : f =ᶠ[𝓝 x] fun y => u y * m y)
    (hdu : |deriv u x| ≤ a * u x)
    (hdl : |deriv (fun y => Real.log (m y)) x| ≤ b) :
    DifferentiableAt ℝ f x ∧ 0 ≤ f x ∧
      deriv f x = m x * (deriv u x + u x * deriv (fun y => Real.log (m y)) x) ∧
      |deriv f x| ≤ f x * (a + b) ∧
      (u x = 0 → f x = 0 ∧ deriv f x = 0) := by sorry

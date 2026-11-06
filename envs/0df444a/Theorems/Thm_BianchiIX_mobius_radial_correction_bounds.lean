-- Prove2me | Theorems.Thm_BianchiIX_mobius_radial_correction_bounds
-- name    : BianchiIX.mobius_radial_correction_bounds
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T07:02:33.578315+00:00
-- url     : https://prove2.me/theorems/8148824a-e3e7-4bba-abde-d3b8481cb324
-- title:
--   The Mobius correction is quadratic in value and linear in radial derivative
-- statement:
--   Let $f:\mathbb R\to\mathbb R$ be differentiable at $x$,
--   $r,K,D\geq0$, $0\leq f(x)\leq1/2$, $f(x)\leq Kr$, and $|f'(x)|\leq D$.
--   For $E(y)=f(y)/(1-f(y))-f(y)$, one has differentiability at $x$ and
--   $$|E(x)|\leq2K^2r^2,\qquad |E'(x)|\leq8KDr.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/MobiusRadialCurve.lean#L7-L38

import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Add

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX

theorem BianchiIX.mobius_radial_correction_bounds {f : ℝ → ℝ} {x r K D : ℝ}
    (hf : DifferentiableAt ℝ f x) (hr : 0 ≤ r) (hK : 0 ≤ K) (hD : 0 ≤ D)
    (hx : 0 ≤ f x ∧ f x ≤ 1 / 2) (hxr : f x ≤ K * r) (hd : |deriv f x| ≤ D) :
    let E := fun a => f a / (1 - f a) - f a
    DifferentiableAt ℝ E x ∧ |E x| ≤ 2 * K ^ 2 * r ^ 2 ∧ |deriv E x| ≤ 8 * K * D * r := by sorry

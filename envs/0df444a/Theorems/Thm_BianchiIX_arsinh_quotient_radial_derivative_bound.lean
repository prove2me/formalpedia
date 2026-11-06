-- Prove2me | Theorems.Thm_BianchiIX_arsinh_quotient_radial_derivative_bound
-- name    : BianchiIX.arsinh_quotient_radial_derivative_bound
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T06:55:23.093211+00:00
-- url     : https://prove2.me/theorems/2ef420fd-316e-441b-863a-22fb735428e9
-- title:
--   An inverse-hyperbolic-sine quotient has a controlled radial derivative
-- statement:
--   Suppose real functions $f,a$ have derivatives $f',a'$ at $t$.
--   Let $r>0$, $M,D\geq0$, and assume
--   $$|f(t)|\leq2Mr,\quad r/2\leq a(t)\leq Mr,\quad |f'|\leq3D,\quad |a'|\leq D.$$
--   Then $h(x)=\operatorname{arsinh}(f(x)/a(x))$ is differentiable at $t$ and
--   $$|h'(t)|\leq20MD/r.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/ArsinhQuotientDerivative.lean#L13-L49

import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX

theorem BianchiIX.arsinh_quotient_radial_derivative_bound {f a : ℝ → ℝ} {f' a' t r M D : ℝ}
    (Hf : HasDerivAt f f' t) (Ha : HasDerivAt a a' t)
    (hr : 0 < r) (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hf : |f t| ≤ 2 * M * r) (ha : r / 2 ≤ a t ∧ a t ≤ M * r)
    (hf' : |f'| ≤ 3 * D) (ha' : |a'| ≤ D) :
    DifferentiableAt ℝ (fun x => Real.arsinh (f x / a x)) t ∧
      |deriv (fun x => Real.arsinh (f x / a x)) t| ≤ 20 * M * D / r := by sorry

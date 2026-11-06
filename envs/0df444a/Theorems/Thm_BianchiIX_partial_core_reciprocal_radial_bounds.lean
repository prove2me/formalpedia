-- Prove2me | Theorems.Thm_BianchiIX_partial_core_reciprocal_radial_bounds
-- name    : BianchiIX.partial_core_reciprocal_radial_bounds
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-06T00:27:27.143877+00:00
-- url     : https://prove2.me/theorems/163ee8cd-4987-4aa3-9f24-e95167dcb700
-- title:
--   Reciprocal phase bounds from partial-core radial errors
-- statement:
--   Let $f,k$ be differentiable at $x$, $0<r\leq1$,
--   $K\geq1$, $U\geq0$, $0\leq P\leq1$, and $C\in\mathbb R$.
--   Assume $k(x)\geq2/(Kr)$, $f(x)\geq k(x)/2$ and
--   $$|f(x)-k(x)|\leq16(U+P^2/k(x)),\quad |k'(x)|\leq K/r^2,$$
--   $$|f'(x)-k'(x)|\leq4CK^2(U+rP)/r^2.$$
--   Then $E=2/f-2/k$ is differentiable at $x$, and
--   $$|f(x)-k(x)|\leq16K(U+rP^2),\quad |E(x)|\leq32K^3r^2(U+rP^2),$$
--   $$|E'(x)|\leq(8CK^4+64K^5)(U+rP).$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/PartialCoreReciprocalError.lean#L25-L79

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

theorem BianchiIX.partial_core_reciprocal_radial_bounds {f k : ℝ → ℝ} {x r K C U P : ℝ}
    (hr : 0 < r ∧ r ≤ 1) (hK : 1 ≤ K) (hU : 0 ≤ U)
    (hP : 0 ≤ P ∧ P ≤ 1) (hf : DifferentiableAt ℝ f x) (hk : DifferentiableAt ℝ k x)
    (hklo : 2 / (K * r) ≤ k x) (hFlo : k x / 2 ≤ f x)
    (hvalue : |f x - k x| ≤ 16 * (U + P ^ 2 / k x))
    (hdk : |deriv k x| ≤ K / r ^ 2)
    (hde : |deriv f x - deriv k x| ≤ 4 * C * K ^ 2 * (U + r * P) / r ^ 2) :
    DifferentiableAt ℝ (fun y => 2 / f y - 2 / k y) x ∧
      |f x - k x| ≤ 16 * K * (U + r * P ^ 2) ∧
      |2 / f x - 2 / k x| ≤ 32 * K ^ 3 * r ^ 2 * (U + r * P ^ 2) ∧
      |deriv (fun y => 2 / f y - 2 / k y) x| ≤
        (8 * C * K ^ 4 + 64 * K ^ 5) * (U + r * P) := by sorry

-- Prove2me | Theorems.Thm_BianchiIX_connection_reciprocal_radial_bounds
-- name    : BianchiIX.connection_reciprocal_radial_bounds
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-06T00:27:23.439254+00:00
-- url     : https://prove2.me/theorems/ed562793-61a8-457b-b48b-ff11b5590b36
-- title:
--   Reciprocal error after a radial decrement of two
-- statement:
--   Let $g,k:\mathbb R\to\mathbb R$ be differentiable at $x$.
--   Assume $0<r\leq1$, $K\geq1$, $C,U\geq0$, $0\leq P\leq1$,
--   $k(x)\geq6$, $k(x)\geq2/(Kr)$, $g(x)\geq k(x)/4$, and
--   $$|k'(x)|\leq K/r^2,\quad |g(x)-(k(x)-2)|\leq C(U+rP^2),$$
--   $$|g'(x)-k'(x)|\leq C(U+rP)/r^2.$$
--   Then $E=2/g-(2/k)/(1-2/k)$ is differentiable at $x$ and
--   $$|E(x)|\leq8CK^2r^2(U+rP^2),\quad
--   |E'(x)|\leq(8CK^2+32CK^4)(U+rP).$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/ConnectionReciprocalCurve.lean#L10-L68

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
open Filter
open scoped Topology

theorem BianchiIX.connection_reciprocal_radial_bounds {g k : ℝ → ℝ} {x r K C U P : ℝ}
    (hr : 0 < r ∧ r ≤ 1) (hK : 1 ≤ K) (hC : 0 ≤ C) (hU : 0 ≤ U)
    (hP : 0 ≤ P ∧ P ≤ 1) (hg : DifferentiableAt ℝ g x) (hk : DifferentiableAt ℝ k x)
    (hk6 : 6 ≤ k x) (hklo : 2 / (K * r) ≤ k x) (hglo : k x / 4 ≤ g x)
    (hdk : |deriv k x| ≤ K / r ^ 2)
    (he : |g x - (k x - 2)| ≤ C * (U + r * P ^ 2))
    (hde : |deriv g x - deriv k x| ≤ C * (U + r * P) / r ^ 2) :
    let E := fun a => 2 / g a - (2 / k a) / (1 - 2 / k a)
    DifferentiableAt ℝ E x ∧ |E x| ≤ 8 * C * K ^ 2 * r ^ 2 * (U + r * P ^ 2) ∧
      |deriv E x| ≤ (8 * C * K ^ 2 + 32 * C * K ^ 4) * (U + r * P) := by sorry

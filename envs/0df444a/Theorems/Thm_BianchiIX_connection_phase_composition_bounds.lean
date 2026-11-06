-- Prove2me | Theorems.Thm_BianchiIX_connection_phase_composition_bounds
-- name    : BianchiIX.connection_phase_composition_bounds
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T06:51:22.333089+00:00
-- url     : https://prove2.me/theorems/5af9d3fd-6329-4436-bc4a-7e554fa54dfe
-- title:
--   Composition of core and connection phase errors preserves amplitude weights
-- statement:
--   Let $0<r\leq1$, $U\geq0$, $0\leq W\leq1$, and
--   $C_0,C_1,C\geq0$. Suppose $f,k,\Delta$ are differentiable at $x$,
--   $g=f-2+\Delta$ near $x$, and
--   $$|f(x)-k(x)|\leq C_0(U+rW^2),\quad |(f-k)'(x)|\leq C_1(U+rW)/r^2,$$
--   $$|\Delta(x)|\leq Cr(U+W^2),\quad |\Delta'(x)|\leq C(U+W^2).$$
--   Then $g$ is differentiable at $x$ and
--   $$|g(x)-(k(x)-2)|\leq(C_0+C_1+C)(U+rW^2),$$
--   $$|g'(x)-k'(x)|\leq(C_0+C_1+C)(U+rW)/r^2.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/ConnectionPhaseComposition.lean#L10-L56

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

theorem BianchiIX.connection_phase_composition_bounds {f k Δ g : ℝ → ℝ} {x r U W C₀ C₁ C : ℝ}
    (hr : 0 < r ∧ r ≤ 1) (hU : 0 ≤ U) (hW : 0 ≤ W ∧ W ≤ 1)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hC : 0 ≤ C)
    (hf : DifferentiableAt ℝ f x) (hk : DifferentiableAt ℝ k x) (hΔ : DifferentiableAt ℝ Δ x)
    (hg : g =ᶠ[𝓝 x] fun a => f a - 2 + Δ a)
    (hfv : |f x - k x| ≤ C₀ * (U + r * W ^ 2))
    (hfd : |deriv (fun a => f a - k a) x| ≤ C₁ * (U + r * W) / r ^ 2)
    (hΔv : |Δ x| ≤ C * r * (U + W ^ 2)) (hΔd : |deriv Δ x| ≤ C * (U + W ^ 2)) :
    DifferentiableAt ℝ g x ∧
      |g x - (k x - 2)| ≤ (C₀ + C₁ + C) * (U + r * W ^ 2) ∧
      |deriv g x - deriv k x| ≤ (C₀ + C₁ + C) * (U + r * W) / r ^ 2 := by sorry

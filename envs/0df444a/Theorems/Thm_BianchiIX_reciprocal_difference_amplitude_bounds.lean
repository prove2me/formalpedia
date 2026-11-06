-- Prove2me | Theorems.Thm_BianchiIX_reciprocal_difference_amplitude_bounds
-- name    : BianchiIX.reciprocal_difference_amplitude_bounds
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T06:59:21.546195+00:00
-- url     : https://prove2.me/theorems/5878f5e9-e05a-4bbc-b913-e375f4a4aeac
-- title:
--   Reciprocal corrections retain amplitude factors in two derivative columns
-- statement:
--   Let $0<\alpha\leq1$, $A,D,u\geq0$, $0\leq v\leq1$,
--   and $p,s\in\mathbb R^3$. Assume
--   $$|\Theta|\leq A\alpha uv,\quad |\psi|\leq2\alpha^2|\Theta|,
--   \quad |p_0|+|p_1|\leq Auv/\alpha^2,\quad |p_2|\leq Au/\alpha^2,$$
--   $$|s_i|\leq2\alpha^2|p_i|+4D\alpha|\Theta|\quad(i=0,1,2).$$
--   Then
--   $$|\psi|\leq10A(D+1)\alpha^3uv,\qquad
--   |s_0|+|s_1|\leq10A(D+1)uv,\qquad |s_2|\leq10A(D+1)u.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/ReciprocalDifference.lean#L77-L109

import Mathlib.Analysis.Calculus.ContDiff.Operations
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

theorem BianchiIX.reciprocal_difference_amplitude_bounds {α A D u v Θ ψ : ℝ} {p s : Fin 3 → ℝ}
    (hα : 0 < α ∧ α ≤ 1) (hA : 0 ≤ A) (hD : 0 ≤ D) (hu : 0 ≤ u) (hv : 0 ≤ v ∧ v ≤ 1)
    (hΘ : |Θ| ≤ A * α * u * v) (hψ : |ψ| ≤ 2 * α ^ 2 * |Θ|)
    (hp : |p 0| + |p 1| ≤ A * u * v / α ^ 2) (hp2 : |p 2| ≤ A * u / α ^ 2)
    (hs : ∀ i, |s i| ≤ 2 * α ^ 2 * |p i| + 4 * D * α * |Θ|) :
    |ψ| ≤ 10 * A * (D + 1) * α ^ 3 * u * v ∧
      |s 0| + |s 1| ≤ 10 * A * (D + 1) * u * v ∧
      |s 2| ≤ 10 * A * (D + 1) * u := by sorry

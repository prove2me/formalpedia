-- Prove2me | Theorems.Thm_FlatlyFoliated_scalar_vacuum_rigidity
-- name    : FlatlyFoliated.scalar_vacuum_rigidity
-- status  : Proved
-- author  : @fizzyinc3
-- created : 2026-10-17T17:50:27.1547+00:00
-- url     : https://prove2.me/theorems/ffb0da09-163e-4a7f-8434-202c3d4049f4
-- title:
--   Scalar vacuum rigidity under approximate spherical symmetry
-- statement:
--   Let $\Lambda>0$ and let $f:\mathbb R^3\to\mathbb R$ be smooth, with $\Delta f>0$ everywhere. Suppose $f$ is approximately spherically symmetric at infinity: writing $g=f-\bar f$ for its difference from its spherical average, $g$ is bounded and $|x|^2\|D^2g(x)\|\|Dg(x)\|\to0$ as $|x|\to\infty$. If
--   $$
--   (\Delta f)^2-\|D^2f\|_F^2=2\Lambda
--   $$
--   throughout $\mathbb R^3$, then there exists $c\in\mathbb R$ such that
--   $$
--   f(x)=\sqrt{\Lambda/12}\,|x|^2+c
--   $$
--   for every $x$. This is the scalar rigidity step in Theorem 5, after the lapse and vector remainder have been eliminated by the maximum principle.
-- source:
--   Bray, Hamm, Hirsch, Wheeler, Zhang, Flatly Foliated Relativity, https://arxiv.org/html/1911.00967v2, Theorem 5 proof, equations (73)–(100); approximate symmetry as in Theorem 5.

import Mathlib
import Definitions.Def_FlatlyFoliatedRelativity_basic

open scoped ContDiff

namespace FlatlyFoliated

/-- Scalar vacuum rigidity, the remaining Hessian equation in the proof of Theorem 5. -/
theorem scalar_vacuum_rigidity (Λ : ℝ) (hΛ : 0 < Λ) (f : R3 → ℝ)
    (hf : ContDiff ℝ ∞ f) (hconv : ∀ x, 0 < lap f x)
    (happrox : ApproxSphSymmAtInfty f)
    (heq : ∀ x, lap f x ^ 2 - hessNormSq f x = 2 * Λ) :
    ∃ c : ℝ, ∀ x, f x = Real.sqrt (Λ / 12) * ‖x‖ ^ 2 + c := by sorry

end FlatlyFoliated

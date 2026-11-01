-- Prove2me | Theorems.Thm_AdditiveConvexity_sensitivity_preserved
-- name    : AdditiveConvexity.sensitivity_preserved
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:51:21.415832+00:00
-- url     : https://prove2.me/theorems/805ca3e4-b613-4802-b3e8-e90edc31d275
-- title:
--   Sensitivity paragraph: a slope bound for $f$ passes to $g$
-- statement:
--   Let $1\le k\le n$, let $I$ be convex, let $f$ be increasing in $x_1,\dots,x_k$ on $V$, and let $g(x)$ be the minimum (1) for every $x\in V$. For $1\le m\le n$ and real $a$: if
--   $$
--   f(x')-f(x)\le a\,(x'_m-x_m)
--   $$
--   for all $x,x'\in V$ agreeing off coordinate $m$ with $x_m\le x'_m$, then the same holds with $g$ in place of $f$.
--
--   This is the step of the proof of Theorem 1 that the paper adds to the classical preservation of additive convexity. Theorem 1 repeats it as its third clause. The case $m=0$ is not claimed.
--
--   Differences from the source:
--   - generalization: ∂f(x)/∂x_m ≤ a for all x in V implies ∂g(x)/∂x_m ≤ a for all x in V → `SlopeLEInCoord` for f implies `SlopeLEInCoord` for g, a bound on difference quotients; reason: g need not be differentiable; the printed hypothesis gives the slope bound by the mean value theorem on a section of V, and the slope bound for g gives every existing partial derivative ≤ a, so the printed clause is a special case
--   - generalization: f additively convex → no convexity hypothesis on f; reason: the statement holds without it, so the printed setting is a special case
--   - reading: `g(x) := min …`, with no existence claim → `IsLeast (f '' transformSet I k x) (g x)` for every x in V; reason: the minimum can fail to exist under every printed hypothesis (I = ℝ, n = k = 1, f(x₀, x₁) = −2x₀ + x₁), and where it fails the printed g is undefined; this is what `min` says, not an infimum
--   - reading: the constraint y_k ≤ x_{k+1} in ℂ(x), which mentions a nonexistent x_{n+1} at k = n → no such constraint at k = n; reason: p.6: at k = n stage n + 1 is an external stage with unlimited supply, and problem (3) has no such bound
--   - reading: increasing in xᵢ on V → `IncreasingInCoord`: only pairs of points of V agreeing off coordinate i are compared; reason: f is defined on V only; p.3 fixes increasing as non-decreasing
--   - encoding: (y₀, …, y_k) together with the tail (x_{k+1}, …, xₙ), with indices 0, …, n → one vector z : Fin (n + 1) → ℝ with z i = x i for i > k; reason: y ↔ z is a bijection and f(y, x_{k+1}, …, xₙ) is f z
--   - encoding: f, g : V → ℝ → total functions on Fin (n + 1) → ℝ, constrained and concluded on V only; reason: Lean convention; no instance changes
-- source:
--   Gong–Wang, Preservation of Additive Convexity, SSRN 3217007 (accepted manuscript), proof of Theorem 1, p.ec3 (PDF p.20)

import Mathlib
import Definitions.Def_AdditiveConvexity_chainDomain
import Definitions.Def_AdditiveConvexity_IncreasingInCoord
import Definitions.Def_AdditiveConvexity_SlopeLEInCoord
import Definitions.Def_AdditiveConvexity_transformSet

namespace AdditiveConvexity

/-- **The sensitivity paragraph.** Gong–Wang, Preservation of Additive Convexity, SSRN 3217007
(accepted manuscript), proof of Theorem 1, p.ec3 (PDF p.20): "`∂f(x)/∂xᵢ ≤ a` implies
`∂g(x)/∂xᵢ ≤ a` for `i = 1, …, n`".

**Formalization Note.** The bound is `SlopeLEInCoord`. Additive convexity of `f` is not assumed:
the statement holds without it. This is a step of the proof of Theorem 1, whose third clause
repeats it under Theorem 1's hypotheses. -/
theorem sensitivity_preserved {n k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) {I : Set ℝ}
    (hI : Convex ℝ I) {f g : (Fin (n + 1) → ℝ) → ℝ}
    (hmono : ∀ m : Fin (n + 1), 1 ≤ m.val → m.val ≤ k → IncreasingInCoord (chainDomain I n) f m)
    (hg : ∀ x ∈ chainDomain I n, IsLeast (f '' transformSet I k x) (g x))
    (m : Fin (n + 1)) (hm : 1 ≤ m.val) (a : ℝ)
    (hf : SlopeLEInCoord (chainDomain I n) f m a) :
    SlopeLEInCoord (chainDomain I n) g m a := by sorry

end AdditiveConvexity

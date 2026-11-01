-- Prove2me | Theorems.Thm_AdditiveConvexity_theorem_1
-- name    : AdditiveConvexity.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:51:18.978554+00:00
-- url     : https://prove2.me/theorems/393d9a31-b122-46dd-bcd5-a0ec834d4327
-- title:
--   Theorem 1: optimal prioritized transformation preserves additive convexity and bounded sensitivity
-- statement:
--   Let $1\le k\le n$, let $I\subseteq\mathbb R$ be convex, and let $V=\{x\in I\times\mathbb R^n\mid x_0\le x_1\le\cdots\le x_n\}$. Suppose $f:V\to\mathbb R$ is additively convex and increasing in $x_1,\dots,x_k$. Let
--   $$
--   g(x)=\min_{y\in\mathbb C(x)}f(y,x_{k+1},\dots,x_n),\tag{1}
--   $$
--   $$
--   \mathbb C(x)=\{y\in I\times\mathbb R^k\mid y_0\le y_1\le\cdots\le y_k\le x_{k+1},\ y_0-x_0\ge y_1-x_1\ge\cdots\ge y_k-x_k\ge 0\},
--   $$
--   the minimum being assumed to exist at every point of $V$, which is what $g(x):=\min$ means. Then:
--
--   1. $g$ is additively convex on $V$;
--   2. $g$ is increasing in $x_1,\dots,x_k$ on $V$;
--   3. for $m=1,\dots,n$ and every real $a$, if $f$ has slope bound $a$ in coordinate $m$ on $V$, then so has $g$.
--
--   This is the paper's first preservation result: for optimal transformation problems whose resources have different priorities, additive convexity and bounded sensitivity pass from the objective to the value function. Theorem 1 does not ask $f$ to be increasing in $x_0$; if it were, the problem would be trivial (p.5).
--
--   Differences from the source:
--   - reading: `g(x) := min …`, with no existence claim → `IsLeast (f '' transformSet I k x) (g x)` for every x in V; reason: the minimum can fail to exist under every printed hypothesis (I = ℝ, n = k = 1, f(x₀, x₁) = −2x₀ + x₁), and where it fails the printed g is undefined; this is what `min` says, not an infimum
--   - reading: the constraint y_k ≤ x_{k+1} in ℂ(x), which mentions a nonexistent x_{n+1} at k = n → no such constraint at k = n; reason: p.6: at k = n stage n + 1 is an external stage with unlimited supply, and problem (3) has no such bound
--   - generalization: ∂f(x)/∂x_m ≤ a for all x in V implies ∂g(x)/∂x_m ≤ a for all x in V → `SlopeLEInCoord` for f implies `SlopeLEInCoord` for g, a bound on difference quotients; reason: g need not be differentiable; the printed hypothesis gives the slope bound by the mean value theorem on a section of V, and the slope bound for g gives every existing partial derivative ≤ a, so the printed clause is a special case
--   - reading: f₀, …, fₙ are univariate convex functions, domain not given (Definition 1) → each φᵢ is convex on the projection of V on coordinate i; reason: the paper's use: ξ₀ minimizes f₀ on I (p.ec2), and f₀ in (EC.21) is convex only on (−∞, 0]; convexity on all of ℝ would exclude it
--   - reading: increasing in xᵢ on V → `IncreasingInCoord`: only pairs of points of V agreeing off coordinate i are compared; reason: f is defined on V only; p.3 fixes increasing as non-decreasing
--   - encoding: (y₀, …, y_k) together with the tail (x_{k+1}, …, xₙ), with indices 0, …, n → one vector z : Fin (n + 1) → ℝ with z i = x i for i > k; reason: y ↔ z is a bijection and f(y, x_{k+1}, …, xₙ) is f z
--   - encoding: f, g : V → ℝ → total functions on Fin (n + 1) → ℝ, constrained and concluded on V only; reason: Lean convention; no instance changes
-- source:
--   Gong–Wang, Preservation of Additive Convexity, SSRN 3217007 (accepted manuscript), Theorem 1, p.4 (PDF p.4)

import Mathlib
import Definitions.Def_AdditiveConvexity_chainDomain
import Definitions.Def_AdditiveConvexity_IncreasingInCoord
import Definitions.Def_AdditiveConvexity_IsAdditivelyConvexOn
import Definitions.Def_AdditiveConvexity_SlopeLEInCoord
import Definitions.Def_AdditiveConvexity_transformSet

namespace AdditiveConvexity

/-- **Theorem 1** (preservation under optimal prioritized transformation). Gong–Wang, Preservation
of Additive Convexity, SSRN 3217007 (accepted manuscript), Theorem 1, p.4 (PDF p.4). Let `f` be
additively convex on `V` and increasing in `x₁, …, x_k`, `1 ≤ k ≤ n`, and let `g` be the minimum
(1). Then `g` is additively convex on `V`, increasing in `x₁, …, x_k` on `V`, and for
`m = 1, …, n` every slope bound `a` for `f` in coordinate `m` is a slope bound for `g`.

**Formalization Note.** `g(x) := min …` is `IsLeast (f '' transformSet I k x) (g x)` for every
`x ∈ V`: the minimum is attained, and no attainment is derived or replaced by an infimum. The
values of `f` and `g` off `V` play no part. `m = 0` is not claimed. -/
theorem theorem_1 {n k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) {I : Set ℝ} (hI : Convex ℝ I)
    {f g : (Fin (n + 1) → ℝ) → ℝ}
    (hconv : IsAdditivelyConvexOn (chainDomain I n) f)
    (hmono : ∀ m : Fin (n + 1), 1 ≤ m.val → m.val ≤ k → IncreasingInCoord (chainDomain I n) f m)
    (hg : ∀ x ∈ chainDomain I n, IsLeast (f '' transformSet I k x) (g x)) :
    IsAdditivelyConvexOn (chainDomain I n) g ∧
      (∀ m : Fin (n + 1), 1 ≤ m.val → m.val ≤ k → IncreasingInCoord (chainDomain I n) g m) ∧
      ∀ m : Fin (n + 1), 1 ≤ m.val → ∀ a : ℝ,
        SlopeLEInCoord (chainDomain I n) f m a → SlopeLEInCoord (chainDomain I n) g m a := by sorry

end AdditiveConvexity

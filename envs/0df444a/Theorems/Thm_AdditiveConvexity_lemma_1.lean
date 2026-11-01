-- Prove2me | Theorems.Thm_AdditiveConvexity_lemma_1
-- name    : AdditiveConvexity.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:50:53.574623+00:00
-- url     : https://prove2.me/theorems/d7b0d246-567f-48ff-8e22-96220a4ccdb7
-- title:
--   Lemma 1: the transformation problem (1) equals the serial problem (4)
-- statement:
--   Let $1\le k\le n$, let $I\subseteq\mathbb R$ be convex, and let $f$ be increasing in $x_1,\dots,x_k$ on the chain domain $V$. Then for every $x\in V$ and every real $v$,
--   $$
--   v=\min_{y\in\mathbb C(x)}f(y,x_{k+1},\dots,x_n)\quad\Longleftrightarrow\quad v=\min_{y\in\hat{\mathbb C}(x)}f(y,x_{k+1},\dots,x_n).
--   $$
--   So either minimum exists exactly when the other does, and they are equal.
--
--   This lemma shows that an optimal transformation problem with prioritized decisions is a serial inventory problem with zero lead times. Additive convexity is not assumed.
--
--   Differences from the source:
--   - reading: `g(x) := min …`, with no existence claim → `IsLeast (f '' transformSet I k x) (g x)` for every x in V; reason: the minimum can fail to exist under every printed hypothesis (I = ℝ, n = k = 1, f(x₀, x₁) = −2x₀ + x₁), and where it fails the printed g is undefined; this is what `min` says, not an infimum
--   - reading: the constraint y_k ≤ x_{k+1} in ℂ(x), which mentions a nonexistent x_{n+1} at k = n → no such constraint at k = n; reason: p.6: at k = n stage n + 1 is an external stage with unlimited supply, and problem (3) has no such bound
--   - reading: increasing in xᵢ on V → `IncreasingInCoord`: only pairs of points of V agreeing off coordinate i are compared; reason: f is defined on V only; p.3 fixes increasing as non-decreasing
--   - encoding: (y₀, …, y_k) together with the tail (x_{k+1}, …, xₙ), with indices 0, …, n → one vector z : Fin (n + 1) → ℝ with z i = x i for i > k; reason: y ↔ z is a bijection and f(y, x_{k+1}, …, xₙ) is f z
--   - encoding: f, g : V → ℝ → total functions on Fin (n + 1) → ℝ, constrained and concluded on V only; reason: Lean convention; no instance changes
-- source:
--   Gong–Wang, Preservation of Additive Convexity, SSRN 3217007 (accepted manuscript), Lemma 1, p.5 (PDF p.5)

import Mathlib
import Definitions.Def_AdditiveConvexity_chainDomain
import Definitions.Def_AdditiveConvexity_IncreasingInCoord
import Definitions.Def_AdditiveConvexity_transformSet
import Definitions.Def_AdditiveConvexity_serialSet

namespace AdditiveConvexity

/-- **Lemma 1** (the serial reformulation). Gong–Wang, Preservation of Additive Convexity,
SSRN 3217007 (accepted manuscript), Lemma 1, p.5 (PDF p.5). If `f` is increasing in
`x₁, …, x_k` on `V`, then for `x ∈ V` the problems (1) and (4) have the same minimum.

**Formalization Note.** The printed `g(x) = min …` is stated as an equivalence of `IsLeast`
statements for every value `v`: a minimum of either problem exists exactly when the other's does,
and they agree. Additive convexity is not assumed, as in the paper. -/
theorem lemma_1 {n k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) {I : Set ℝ} (hI : Convex ℝ I)
    {f : (Fin (n + 1) → ℝ) → ℝ}
    (hmono : ∀ m : Fin (n + 1), 1 ≤ m.val → m.val ≤ k → IncreasingInCoord (chainDomain I n) f m)
    {x : Fin (n + 1) → ℝ} (hx : x ∈ chainDomain I n) (v : ℝ) :
    IsLeast (f '' transformSet I k x) v ↔ IsLeast (f '' serialSet I k x) v := by sorry

end AdditiveConvexity

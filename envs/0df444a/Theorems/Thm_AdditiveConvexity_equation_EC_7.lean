-- Prove2me | Theorems.Thm_AdditiveConvexity_equation_EC_7
-- name    : AdditiveConvexity.equation_EC_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:51:37.195167+00:00
-- url     : https://prove2.me/theorems/4ef9e8f0-46fc-4023-ad6e-882e9a34f4d9
-- title:
--   Equation (EC.7): the explicit additive decomposition of $g$
-- statement:
--   Let $1\le k\le n$, let $I$ be convex, let $f(x)=\sum_{i=0}^n\varphi_i(x_i)$ on $V$ with each $\varphi_i$ convex on the projection of $V$ on coordinate $i$, let $f$ be increasing in $x_1,\dots,x_k$ on $V$, and let $g(x)$ be the minimum (1) for every $x\in V$. Then there are $G_0,\dots,G_k$, each convex and increasing on the projection of $V$ on its coordinate, and $H$ convex and decreasing on the upward closure of $I$, such that for every $x\in V$,
--   $$
--   g(x)=\sum_{i=0}^{k}G_i(x_i)+H(x_{k+1})+\sum_{i=k+1}^{n}\varphi_i(x_i),
--   $$
--   where the term $H(x_{k+1})$ is absent when $k=n$.
--
--   The decomposition shows that $g$ is additively convex, and it is the formula from which the paper reads off the monotonicity of $g$.
--
--   Differences from the source:
--   - reading: `g(x) := min …`, with no existence claim → `IsLeast (f '' transformSet I k x) (g x)` for every x in V; reason: the minimum can fail to exist under every printed hypothesis (I = ℝ, n = k = 1, f(x₀, x₁) = −2x₀ + x₁), and where it fails the printed g is undefined; this is what `min` says, not an infimum
--   - reading: the term h_k(x_{k+1}) of (EC.7), with x_{k+1} nonexistent at k = n → a case split on k < n, with the term 0 at k = n; reason: as in ℂ(x); p.6: there is no stage n + 1 to bound y_n
--   - reading: gᵢ and h_k given through minimizers ξᵢ by (EC.2) to (EC.6) → existentially quantified G i and H with the properties the proof states; reason: the ξᵢ need not exist (I = ℝ, f₀(x) = e^{−x}) and the ordering of them needs a compatible choice; Lemma EC.1's first sentence is the existence claim the paper relies on
--   - reading: f₀, …, fₙ are univariate convex functions, domain not given (Definition 1) → each φᵢ is convex on the projection of V on coordinate i; reason: the paper's use: ξ₀ minimizes f₀ on I (p.ec2), and f₀ in (EC.21) is convex only on (−∞, 0]; convexity on all of ℝ would exclude it
--   - reading: increasing in xᵢ on V → `IncreasingInCoord`: only pairs of points of V agreeing off coordinate i are compared; reason: f is defined on V only; p.3 fixes increasing as non-decreasing
--   - encoding: (y₀, …, y_k) together with the tail (x_{k+1}, …, xₙ), with indices 0, …, n → one vector z : Fin (n + 1) → ℝ with z i = x i for i > k; reason: y ↔ z is a bijection and f(y, x_{k+1}, …, xₙ) is f z
--   - encoding: f, g : V → ℝ → total functions on Fin (n + 1) → ℝ, constrained and concluded on V only; reason: Lean convention; no instance changes
-- source:
--   Gong–Wang, Preservation of Additive Convexity, SSRN 3217007 (accepted manuscript), proof of Theorem 1, equation (EC.7), p.ec3 (PDF p.20), with the properties of gᵢ and h_k from pp.ec1–ec2 (PDF pp.18–19)

import Mathlib
import Definitions.Def_AdditiveConvexity_chainDomain
import Definitions.Def_AdditiveConvexity_IncreasingInCoord
import Definitions.Def_AdditiveConvexity_IsAdditivelyConvexOn
import Definitions.Def_AdditiveConvexity_transformSet

namespace AdditiveConvexity

/-- **Equation (EC.7)** (the explicit additive decomposition of `g`). Gong–Wang, Preservation of
Additive Convexity, SSRN 3217007 (accepted manuscript), proof of Theorem 1, equation (EC.7), p.ec3
(PDF p.20), with the properties of `gᵢ` and `h_k` from pp.ec1–ec2 (PDF pp.18–19):
`g(x) = ∑_{i=0}^k gᵢ(xᵢ) + h_k(x_{k+1}) + ∑_{i=k+1}^n fᵢ(xᵢ)`, with `gᵢ` convex and increasing and
`h_k` convex and decreasing.

**Formalization Note.** `G i` is convex and monotone on the projection of `V` on coordinate `i`,
which is `I` for `i = 0` and the upward closure of `I` otherwise; `H` is convex and antitone on
the upward closure of `I`. There is no term `h_k(x_{k+1})` at `k = n`: the bracket is `0` there
(p.6, PDF p.6: stage `n + 1` is an external stage with unlimited supply). The minimum (1) is `IsLeast`. -/
theorem equation_EC_7 {n k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) {I : Set ℝ} (hI : Convex ℝ I)
    {f g : (Fin (n + 1) → ℝ) → ℝ} {φ : Fin (n + 1) → ℝ → ℝ}
    (hφ : IsAdditiveConvexDecomposition (chainDomain I n) f φ)
    (hmono : ∀ m : Fin (n + 1), 1 ≤ m.val → m.val ≤ k → IncreasingInCoord (chainDomain I n) f m)
    (hg : ∀ x ∈ chainDomain I n, IsLeast (f '' transformSet I k x) (g x)) :
    ∃ (G : Fin (n + 1) → ℝ → ℝ) (H : ℝ → ℝ),
      (∀ i : Fin (n + 1), i.val ≤ k →
        ConvexOn ℝ ((fun x : Fin (n + 1) → ℝ => x i) '' chainDomain I n) (G i) ∧
          MonotoneOn (G i) ((fun x : Fin (n + 1) → ℝ => x i) '' chainDomain I n)) ∧
      ConvexOn ℝ (upperClosure I : Set ℝ) H ∧ AntitoneOn H (upperClosure I : Set ℝ) ∧
      ∀ x ∈ chainDomain I n,
        g x = ∑ i : Fin (n + 1) with i.val ≤ k, G i (x i) +
            (if h : k < n then H (x ⟨k + 1, by omega⟩) else 0) +
          ∑ i : Fin (n + 1) with k < i.val, φ i (x i) := by sorry

end AdditiveConvexity

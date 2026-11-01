-- Prove2me | Theorems.Thm_ConstrainedTrading_lemma_2_2_linSet_mnat
-- name    : ConstrainedTrading.lemma_2_2_linSet_mnat
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:21:48.98062+00:00
-- url     : https://prove2.me/theorems/28037094-3db7-4fa9-9d9b-7abd4a74205e
-- title:
--   Lemma 2.2 (corrected: M$^\sharp$-convex, not M-convex) — $B_f(x)$ is M$^\sharp$-convex
-- statement:
--   Let $f:\mathbb Z^E\to\mathbb R\cup\{-\infty\}$ be M$^\sharp$-concave and let $x\in\mathbb R^E$ lie in the convex hull of $\operatorname{dom} f$. Then the set $B_f(x)$, the points of the unit hypercube $N(x)$ that carry positive weight in an optimal convex representation of $x$ (one attaining $\hat f(x)$), is M$^\sharp$-convex.
--
--   Lemma 2.2 says that the concave extension of an M$^\sharp$-concave function is linear on a discretely convex cell around every point. Together with Theorem 2.2 it is the key to Theorem 2.3: a fractional optimum lies in the convex hull of an M$^\sharp$-convex set of integer points on which $\hat f$ is linear.
--
--   **Formalization Note** $\operatorname{dom}f=\{z : f(z)\ne-\infty\}$ and its convex hull is taken in $\mathbb R^E$; $B_f(x)$ is `linSet f x`.
--
--   Differences from the source:
--
--   - correction: Bf(x) is an M-convex set → Bf(x) is an M♯-convex set; reason: E = {e}, f ≡ 0, x = 1/2: N(x) = {0,1}, f̂(x) = 0, Bf(x) = {0,1}; for x₁ = 1, x₂ = 0, u = e the set supp⁻(x₁ − x₂) is empty, so no exchange v exists; the proof on pp.6–7 establishes M♯-convexity
--   - reading: B_f(x) = {z ∈ N(x) ‖ ∃λ, Σλ_z = 1, Σλ_z z = x, Σλ_z f(z) = f̂(x)} (Def 2.10, p.6, garbled) → z ∈ N(x) = {z : ⌊x⌋ ≤ z ≤ ⌈x⌉} with positive weight in some optimal convex representation of x supported in N(x), f̂ being the concave extension; reason: the proof of Lemma 2.2 uses λ_{x₁} > 0 and λ_{x₂} > 0; without λ_z > 0 the set would be all of N(x) or empty; N(x), 'the unit hypercube containing x', is read as the smallest integer box containing x (in any unit cube containing x, a point of positive weight agrees with x at its integer coordinates, so the set is the same); the page's 'convex extension of function f' is the concave extension of Definition 2.9 for concave f, as in §2.2 and §3
--   - reading: concave extension f̂(x) = max{Σ_z λ_z f(z) : Σ_z λ_z z = x, 0 ≤ λ_z ≤ 1, Σ_z λ_z = 1} (Defs 2.8–2.9, p.5) → f̂(x) = sSup over finite convex representations in EReal, sup ∅ = −∞; reason: a max need not be attained for a general f; the sup is the total version, and it is the convex-combination hull, not the closed concave closure
--   - reading: M♯-concave f : ℤ^E → R, exchange 'for all x, y ∈ B' with B unnamed (Def 2.7, p.4; p.5) → f : ℤ^E → ℝ ∪ {−∞}, exchange for x, y ∈ dom f = {z : f z ≠ −∞}; reason: the paper's valuations take values in ℝ ∪ {−∞} (p.3, footnote 3) and p.5 defines dom f; the real-valued case is dom f = ℤ^E
-- source:
--   Kizilkale, Vohra, Constrained Trading Networks, arXiv:2008.09757v1, Lemma 2.2, p.6

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexSetsB_IntEmbed
import Definitions.Def_ConstrainedTrading_MNatConvexSet
import Definitions.Def_ConstrainedTrading_MNatConcave
import Definitions.Def_ConstrainedTrading_linSet

open DiscreteConvex.MConvexSetsB

namespace ConstrainedTrading

/-- **Lemma 2.2** (Kizilkale–Vohra, *Constrained Trading Networks*, arXiv:2008.09757v1, p.6;
corrected: M♯-convex, not M-convex). For every M♯-concave `f : ℤ^E → ℝ ∪ {−∞}` and every `x` in
the convex hull of `dom f`, the set `B_f(x)` is M♯-convex.

**Formalization Note** `dom f = {z | f z ≠ ⊥}`; its convex hull is taken in `ℝ^E` through
`IntEmbed`. `B_f(x)` is `linSet f x` (Definition 2.10 under reading R4). The page says
"M-convex"; that is false: for `E = {e}`, `f ≡ 0` and `x = 1/2`, `B_f(x) = {0, 1}`, and for
`x₁ = 1`, `x₂ = 0`, `u = e` the set `supp⁻(x₁ − x₂)` is empty, so no exchange `v` exists. The
proof on pp.6–7 establishes M♯-convexity. -/
theorem lemma_2_2_linSet_mnat {E : Type*} [Fintype E] [DecidableEq E]
    (f : (E → ℤ) → WithBot ℝ) (hf : MNatConcave f) (x : E → ℝ)
    (hx : x ∈ convexHull ℝ (IntEmbed {z : E → ℤ | f z ≠ ⊥})) :
    MNatConvexSet (linSet f x) := by sorry

end ConstrainedTrading

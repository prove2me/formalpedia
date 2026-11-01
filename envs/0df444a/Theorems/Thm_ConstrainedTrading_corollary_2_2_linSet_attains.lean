-- Prove2me | Theorems.Thm_ConstrainedTrading_corollary_2_2_linSet_attains
-- name    : ConstrainedTrading.corollary_2_2_linSet_attains
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:21:40.517746+00:00
-- url     : https://prove2.me/theorems/f66a6086-a5dc-425d-9819-878bcc35414f
-- title:
--   Corollary 2.2 — every probability vector on $B_f(x)$ with mean $x$ attains $\hat f(x)$
-- statement:
--   Let $f:\mathbb Z^E\to\mathbb R\cup\{-\infty\}$ and $x\in\mathbb R^E$. For every probability vector $\lambda$ supported in $B_f(x)$ with $\sum_{z\in B_f(x)}\lambda_z z=x$,
--   $$
--   \hat f(x)=\sum_z\lambda_z f(z).
--   $$
--
--   So $\hat f$ is computed by any convex representation of $x$ that uses only points of $B_f(x)$; in the proof of Theorem 2.3 this is applied to the representation obtained from Theorem 2.2.
--
--   **Formalization Note** A probability vector supported in $B_f(x)$ is a finite set $S\subseteq B_f(x)$ with weights $\lambda>0$ on $S$, $\sum\lambda=1$, $\sum\lambda_z z=x$. Values are in `EReal`.
--
--   Differences from the source:
--
--   - generalization: stated after Lemma 2.2, in its setting (f M♯-concave, x in the convex hull of dom f) → every f : ℤ^E → ℝ ∪ {−∞} and every x ∈ ℝ^E; reason: the conclusion does not use M♯-concavity ('Proof follows trivially from the definition of Bf(x)'); the paper's setting is a special case
--   - encoding: probability vector λ on Bf(x) → finite S ⊆ Bf(x) with weights λ > 0 on S; reason: points of weight 0 are dropped; same instances
--   - reading: B_f(x) = {z ∈ N(x) ‖ ∃λ, Σλ_z = 1, Σλ_z z = x, Σλ_z f(z) = f̂(x)} (Def 2.10, p.6, garbled) → z ∈ N(x) = {z : ⌊x⌋ ≤ z ≤ ⌈x⌉} with positive weight in some optimal convex representation of x supported in N(x), f̂ being the concave extension; reason: the proof of Lemma 2.2 uses λ_{x₁} > 0 and λ_{x₂} > 0; without λ_z > 0 the set would be all of N(x) or empty; N(x), 'the unit hypercube containing x', is read as the smallest integer box containing x (in any unit cube containing x, a point of positive weight agrees with x at its integer coordinates, so the set is the same); the page's 'convex extension of function f' is the concave extension of Definition 2.9 for concave f, as in §2.2 and §3
--   - reading: concave extension f̂(x) = max{Σ_z λ_z f(z) : Σ_z λ_z z = x, 0 ≤ λ_z ≤ 1, Σ_z λ_z = 1} (Defs 2.8–2.9, p.5) → f̂(x) = sSup over finite convex representations in EReal, sup ∅ = −∞; reason: a max need not be attained for a general f; the sup is the total version, and it is the convex-combination hull, not the closed concave closure
-- source:
--   Kizilkale, Vohra, Constrained Trading Networks, arXiv:2008.09757v1, Corollary 2.2, p.7

import Mathlib
import Definitions.Def_ConstrainedTrading_IsConvexRep
import Definitions.Def_ConstrainedTrading_repValue
import Definitions.Def_ConstrainedTrading_concaveExt
import Definitions.Def_ConstrainedTrading_linSet

namespace ConstrainedTrading

/-- **Corollary 2.2** (Kizilkale–Vohra, *Constrained Trading Networks*, arXiv:2008.09757v1,
p.7). For every probability vector `λ` supported in `B_f(x)` with `Σ_{z∈B_f(x)} λ_z z = x`, one
has `f̂(x) = Σ_z λ_z f(z)`.

**Formalization Note** A probability vector supported in `B_f(x)` is a finite set
`S ⊆ B_f(x) = linSet f x` with weights `λ > 0` on `S`, `Σ λ = 1`, `Σ λ_z z = x`
(`IsConvexRep`; points of weight `0` are dropped from `S`). The statement is made for every
`f : ℤ^E → ℝ ∪ {−∞}`, without the M♯-concavity under which the paper states Lemma 2.2; this is a
generalization that specializes to the paper's setting. Values are in `EReal`. -/
theorem corollary_2_2_linSet_attains {E : Type*} (f : (E → ℤ) → WithBot ℝ) (x : E → ℝ)
    (S : Finset (E → ℤ)) (wt : (E → ℤ) → ℝ) (hS : (↑S : Set (E → ℤ)) ⊆ linSet f x)
    (hrep : IsConvexRep x S wt) :
    concaveExt f x = repValue f S wt := by sorry

end ConstrainedTrading

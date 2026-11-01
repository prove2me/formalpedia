-- Prove2me | Theorems.Thm_ConstrainedTrading_theorem_2_2_mnat_intersection_hull
-- name    : ConstrainedTrading.theorem_2_2_mnat_intersection_hull
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:19:27.803473+00:00
-- url     : https://prove2.me/theorems/53fc6c1e-ed28-4caf-839b-1465374c78a8
-- title:
--   Theorem 2.2 for M$^\sharp$-convex sets (corrected: $\cap$ for the display's $\cup$) — $\overline{B_1\cap B_2}=\overline{B_1}\cap\overline{B_2}$
-- statement:
--   Let $V$ be a finite set and let $B_1,B_2\subseteq\mathbb Z^V$ be M$^\sharp$-convex sets. Then the convex hull of their intersection equals the intersection of their convex hulls:
--   $$
--   \operatorname{conv}(B_1\cap B_2)=\operatorname{conv}B_1\cap\operatorname{conv}B_2 ,
--   $$
--   the convex hulls being taken in $\mathbb R^V$.
--
--   The paper quotes this as Theorem 2.2 (Murota's Theorem 4.22) for M-convex sets, and the proof of Theorem 2.3 applies it to a face of the polymatroid and to $B_f(x)$, which are M$^\sharp$-convex. This item states the theorem in the generality in which the paper uses it.
--
--   **Formalization Note** $\operatorname{conv}B$ is `convexHull ℝ (IntEmbed B)`. No nonemptiness is assumed (for an empty set both sides are empty).
--
--   Differences from the source:
--
--   - generalization: M-convex sets B₁ and B₂ → M♯-convex sets B₁, B₂, not required nonempty; reason: the proof of Theorem 2.3 (p.7) applies Theorem 2.2 to M♯-convex sets; every M-convex set is M♯-convex, so this specializes to the paper's statement
--   - correction: display B̄₁ ∩ B̄₂ = conv(B₁ ∪ B₂) → conv(B₁ ∩ B₂) = conv B₁ ∩ conv B₂; reason: the words say 'the convex closure of their intersection'; with ∪ the display is false: B₁ = {0}, B₂ = {1} ⊂ ℤ give conv B₁ ∩ conv B₂ = ∅ ≠ [0,1]
--   - encoding: convex closure B̄ → convexHull ℝ of the real image IntEmbed B; reason: Murota's B̄ is the convex hull of B in ℝ^V; same object
-- source:
--   Kizilkale, Vohra, Constrained Trading Networks, arXiv:2008.09757v1, Theorem 2.2, p.6, as applied in the proof of Theorem 2.3, p.7

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexSetsB_IntEmbed
import Definitions.Def_ConstrainedTrading_MNatConvexSet

open DiscreteConvex.MConvexSetsB

namespace ConstrainedTrading

/-- **Theorem 2.2 for M♯-convex sets** (Kizilkale–Vohra, *Constrained Trading Networks*,
arXiv:2008.09757v1, Theorem 2.2, p.6, in the generality in which the proof of Theorem 2.3,
p.7, applies it, namely to the M♯-convex sets `F_x` and `B_f(x)`): for M♯-convex sets
`B₁, B₂ ⊆ ℤ^V`, the convex hull of their intersection equals the intersection of their convex
hulls, `conv(B₁ ∩ B₂) = conv B₁ ∩ conv B₂`.

**Formalization Note** `IntEmbed B` is the image of `B` in `ℝ^V`. The paper states Theorem 2.2
(Murota's Theorem 4.22) for M-convex sets; every M-convex set is M♯-convex, so this specializes
to it (the M-convex case is the published `DiscreteConvex.MConvexSetsB.mconvex_intersection_hull`).
No nonemptiness is assumed: for an empty `Bᵢ` both sides are empty. The printed display has
`∪` under the bar on the right; the words ("the convex closure of their intersection") give `∩`. -/
theorem theorem_2_2_mnat_intersection_hull {V : Type*} [Fintype V] [DecidableEq V]
    (B1 B2 : Set (V → ℤ)) (h1 : MNatConvexSet B1) (h2 : MNatConvexSet B2) :
    convexHull ℝ (IntEmbed (B1 ∩ B2)) = convexHull ℝ (IntEmbed B1) ∩ convexHull ℝ (IntEmbed B2) := by sorry

end ConstrainedTrading

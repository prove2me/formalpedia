-- Prove2me | Theorems.Thm_ConstrainedTrading_polymatroid_face_mnat_integral
-- name    : ConstrainedTrading.polymatroid_face_mnat_integral
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:19:38.058681+00:00
-- url     : https://prove2.me/theorems/8124b135-ab65-4f91-95a3-53e0707c4321
-- title:
--   Faces of an integral polymatroid (corrected: M$^\sharp$-convex, not M-convex) — integer points M$^\sharp$-convex, face integral
-- statement:
--   Let $E$ be a finite set, $\rho:2^E\to\mathbb Z$ submodular, and $P(\rho)=\{x\ge0:\ \sum_{e\in S}x_e\le\rho(S)\ \forall S\}$ the associated integral polymatroid. Let $F$ be a face of $P(\rho)$, that is, a convex subset of $P(\rho)$ such that whenever an open segment between two points of $P(\rho)$ meets $F$, both endpoints lie in $F$. Then
--
--   1. the set of integer points $F\cap\mathbb Z^E$ is M$^\sharp$-convex, and
--   2. $F\subseteq\operatorname{conv}(F\cap\mathbb Z^E)$.
--
--   This is the fact used in the proof of Theorem 2.3 for the face $F_x$ of the polymatroid containing an optimizer $x$: it is treated as an M$^\sharp$-convex set of integer points whose convex hull contains $x$. Taking $F=P(\rho)$ gives that the integer points of an integral polymatroid form an M$^\sharp$-convex set and that $P(\rho)$ is an integral polytope.
--
--   **Formalization Note** A face is `Convex ℝ F ∧ IsExtreme ℝ (polymatroid ρ) F`; $F=P(\rho)$ and $F=\emptyset$ are included.
--
--   Differences from the source:
--
--   - correction: Fx is an M-convex set → the integer points of F form an M♯-convex set; reason: E = {e}, ρ(∅) = 0, ρ({e}) = 1: P(ρ) = [0,1] has integer points {0, 1}, and for x = 1, y = 0, u = e no v ∈ supp⁻(x − y) = ∅ exists, so {0,1} is not M-convex; it is M♯-convex, which is all the proof of Theorem 2.3 needs
--   - reading: Fx, the face of the polymatroid containing x, used as a set of integer points with x in its convex closure → any face F (convex extreme subset of P(ρ)); conclusion on F ∩ ℤ^E plus F ⊆ conv(F ∩ ℤ^E); reason: the proof writes x ∈ F̄x ∩ B̄f(x) and applies Theorem 2.2 to Fx as a discrete set, which identifies the face with its integer points
--   - reading: integral polymatroid P_f = {x ∈ ℝ^E : Σ_{e∈S} x_e ≤ f(S) ∀S ⊆ E} (p.4, no sign constraint) → P(ρ) = {x : x ≥ 0, Σ_{e∈S} x_e ≤ ρ(S) ∀S}; reason: standard meaning of polymatroid, outcomes are x ∈ ℤ₊^E (p.3); without x ≥ 0 Theorems 2.3 and 3.1, which use this item, are false (E = {e}, ρ ≡ 0, seller valuation w(z) = −z: the objective −x is unbounded on (−∞, 0])
-- source:
--   Kizilkale, Vohra, Constrained Trading Networks, arXiv:2008.09757v1, proof of Theorem 2.3, p.7 ("Else let Fx be the face of B that contains x. Fx is an M-convex set …"); p.4 ("the M-convex set B in Corollary 2.1 is precisely Pf")

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexSetsB_IntEmbed
import Definitions.Def_ConstrainedTrading_MNatConvexSet
import Definitions.Def_SteinitzExchange_Duality_SetFunction
import Definitions.Def_ConstrainedTrading_polymatroid

open DiscreteConvex.MConvexSetsB

namespace ConstrainedTrading

/-- **Faces of an integral polymatroid** (Kizilkale–Vohra, *Constrained Trading Networks*,
arXiv:2008.09757v1, p.4, "the M-convex set B in Corollary 2.1 is precisely P_f", and the proof
of Theorem 2.3, p.7, "let F_x be the face of B that contains x. F_x is an M-convex set (as we
have seen earlier M-convex sets are essentially polymatroids)"; corrected to M♯).
Let `ρ : 2^E → ℤ` be submodular and let `F` be a face of the polymatroid `P(ρ)`, i.e. a convex
extreme subset. Then the integer points of `F` form an M♯-convex set, and `F` is contained in
the convex hull of its integer points.

**Formalization Note** A face is `Convex ℝ F ∧ IsExtreme ℝ (polymatroid ρ) F` (a convex subset
such that any open segment of `P(ρ)` meeting `F` has both endpoints in `F`); `F = P(ρ)` and
`F = ∅` are included. The integer points of `F` are `{z : E → ℤ | (z : ℝ^E) ∈ F}`. The page
says "M-convex"; that is false (for `E = {e}`, `ρ(∅) = 0`, `ρ({e}) = 1`, the integer points of
`P(ρ) = [0,1]` are `{0, 1}`, which is not M-convex), and the proof of Theorem 2.3 needs only
M♯-convexity. -/
theorem polymatroid_face_mnat_integral {E : Type*} [Fintype E] [DecidableEq E]
    (ρ : Finset E → ℤ) (hρ : SteinitzExchange.Duality.IsSubmodular ρ) (F : Set (E → ℝ)) (hFc : Convex ℝ F)
    (hF : IsExtreme ℝ (polymatroid ρ) F) :
    MNatConvexSet {z : E → ℤ | (fun e => (z e : ℝ)) ∈ F} ∧
      F ⊆ convexHull ℝ (IntEmbed {z : E → ℤ | (fun e => (z e : ℝ)) ∈ F}) := by sorry

end ConstrainedTrading

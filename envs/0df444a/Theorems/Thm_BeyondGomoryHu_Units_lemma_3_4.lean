-- Prove2me | Theorems.Thm_BeyondGomoryHu_Units_lemma_3_4
-- name    : BeyondGomoryHu.Units.lemma_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:49:50.489396+00:00
-- url     : https://prove2.me/theorems/01b0c1cb-0edd-4d76-86b5-12b2a120c83c
-- title:
--   Lemma 3.4 — distinctness in the LCA (corrected: S-cut meets S on both sides)
-- statement:
--   Throughout, $G=(V,E,w)$ is a connected undirected graph with positive integer weights (the standing assumption of Section 2), $\mu$ is a non-leaf node of the skeleton hierarchy $\mathcal T$ and $(H_\mu,\pi_\mu)$ is a connectivity carcass of $\mu$.
--
--   Let $\mu=\mathrm{LCA}_{\mathcal T}(x,y)$ with children $\alpha\ni x$, $\beta\ni y$, and let $u,v$ be vertices whose $x,y$-units do not intersect $\mu$. Then
--   $$\phi_{x,y}(u)=\phi_{x,y}(v)\iff\phi_\mu(u)=\phi_\mu(v).$$
--
--   The split vertices at the LCA are therefore grouped into units by their $\mu$-unit identifiers.
--
--   **Formalization Note.** The carcass is a hypothesis `IsCarcass G μ K` (the properties of Theorems 2.2–2.3); a projection is stored by its two endpoints and its nodes/edges are those of the unique proper path between them. A component is a set of nodes of $H_\mu$, identified with the set of terminals it contains (`compTerms`) when compared with vertex sets. Relations between sets use `SameUnitSets` and `SetPrec` (all pairs).
--
--   Differences from the source:
--   - correction: an S-cut is a set A with A ∩ S = ∅ and Ā ∩ S ≠ ∅ (p. 3, as printed) → an S-cut meets S on both sides: A ∩ S ≠ ∅ and Ā ∩ S ≠ ∅ (IsCut); reason: as printed, A = ∅ is an S-cut of capacity 0, so in the connected path a–b (weight 1) with S = {a,b} the only S-mincut is ∅; then no (x,y)-mincut exists and Theorem 2.2 fails; every proof (e.g. App. B, "s1 ∈ S ∩ A, s2 ∈ S ∩ Ā") uses the corrected definition
--   - encoding: G = (V, E, w) with w : E → Z+ → a finite vertex type V (Fin n in the goal) and a symmetric weight function w : V → V → ℕ, 0 meaning no edge; reason: same capacities of every vertex set: parallel edges add up and loops cross no cut
--   - generalization: the carcass of µ (the skeleton H_µ of Theorem 2.2 with the projections of Theorem 2.3) → any carcass data K satisfying IsCarcass G µ K, i.e. the properties listed in Theorems 2.2 and 2.3; reason: the paper uses only these properties ("It assumes only the preliminary tools from Section 2 as black boxes", p. 4); its carcass satisfies them, so the statement specializes to the source
--   - encoding: µ = LCA_T(x, y), with children α ∋ x and β ∋ y → a node µ of T with |µ| ≥ 2, a carcass K of µ, and nonempty nodes a ≠ b of H_µ with x ∈ α, y ∈ β; reason: the children of µ are exactly the nonempty nodes of H_µ (Theorem 2.2), so x and y lie in different children iff µ = LCA_T(x, y)
-- source:
--   Koustav Bhanja, Merav Parter, Asaf Petruschka, STOC 2027 submission #1544 (October 2026), Lemma 3.4 (Distinctness in LCA), p. 6 (PDF 8)

import Mathlib
import Definitions.Def_BeyondGomoryHu_Units_Hierarchy

set_option autoImplicit false

namespace BeyondGomoryHu.Units

theorem lemma_3_4 {V : Type} [Fintype V] [DecidableEq V] (G : WGraph V) (hG : G.Connected) (μ : Finset V) (hμ : IsNode G μ) (hμ2 : 2 ≤ μ.card)
    {N : Type} [Fintype N] (K : Carcass V N) (hK : IsCarcass G μ K)
    (a b : N) (hab : a ≠ b) (x y : V) (hx : x ∈ K.terms a) (hy : y ∈ K.terms b) (u v : V)
    (hu : ∀ t ∈ μ, ¬ SameUnit G x y u t) (hv : ∀ t ∈ μ, ¬ SameUnit G x y v t) :
    SameUnit G x y u v ↔ SEquiv G μ u v := by sorry

end BeyondGomoryHu.Units

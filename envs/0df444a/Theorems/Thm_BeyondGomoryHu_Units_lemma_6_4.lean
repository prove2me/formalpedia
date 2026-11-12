-- Prove2me | Theorems.Thm_BeyondGomoryHu_Units_lemma_6_4
-- name    : BeyondGomoryHu.Units.lemma_6_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:52:14.78705+00:00
-- url     : https://prove2.me/theorems/f68dced3-2c4b-4d20-a275-b71d8ad7adc5
-- title:
--   Lemma 6.4 — the traversal list is a topological order (corrected: S-cut meets S on both sides)
-- statement:
--   Throughout, $G=(V,E,w)$ is a connected undirected graph with positive integer weights (the standing assumption of Section 2), $\mu$ is a non-leaf node of the skeleton hierarchy $\mathcal T$ and $(H_\mu,\pi_\mu)$ is a connectivity carcass of $\mu$.
--
--   Let $\mu=\mathrm{LCA}_{\mathcal T}(x,y)$ with children $\alpha\ni x$, $\beta\ni y$, and let $T_1,\dots,T_k$ be the list of $\alpha\beta$-components obtained by traversing $P_{\alpha\beta}$ from $\alpha$ to $\beta$, reporting at each cycle with entry $\gamma$ and exit $\delta$ first the components of one semi-cycle from $\gamma$ to $\delta$ and then those of the other. The list is a topological order of the $\alpha\beta$-components:
--   $$\forall i<j:\ T_j\not\preceq_{(x,y)}T_i.$$
--
--   **Formalization Note.** The carcass is a hypothesis `IsCarcass G μ K` (the properties of Theorems 2.2–2.3); a projection is stored by its two endpoints and its nodes/edges are those of the unique proper path between them. A component is a set of nodes of $H_\mu$, identified with the set of terminals it contains (`compTerms`) when compared with vertex sets. Relations between sets use `SameUnitSets` and `SetPrec` (all pairs). The list is any `IsTraversalList`: a list of all $\alpha\beta$-components sorted by the traversal key of a simple $\alpha$–$\beta$ path $Q$, which fixes the semi-cycles reported first.
--
--   Differences from the source:
--   - correction: an S-cut is a set A with A ∩ S = ∅ and Ā ∩ S ≠ ∅ (p. 3, as printed) → an S-cut meets S on both sides: A ∩ S ≠ ∅ and Ā ∩ S ≠ ∅ (IsCut); reason: as printed, A = ∅ is an S-cut of capacity 0, so in the connected path a–b (weight 1) with S = {a,b} the only S-mincut is ∅; then no (x,y)-mincut exists and Theorem 2.2 fails; every proof (e.g. App. B, "s1 ∈ S ∩ A, s2 ∈ S ∩ Ā") uses the corrected definition
--   - encoding: G = (V, E, w) with w : E → Z+ → a finite vertex type V (Fin n in the goal) and a symmetric weight function w : V → V → ℕ, 0 meaning no edge; reason: same capacities of every vertex set: parallel edges add up and loops cross no cut
--   - generalization: the carcass of µ (the skeleton H_µ of Theorem 2.2 with the projections of Theorem 2.3) → any carcass data K satisfying IsCarcass G µ K, i.e. the properties listed in Theorems 2.2 and 2.3; reason: the paper uses only these properties ("It assumes only the preliminary tools from Section 2 as black boxes", p. 4); its carcass satisfies them, so the statement specializes to the source
--   - encoding: µ = LCA_T(x, y), with children α ∋ x and β ∋ y → a node µ of T with |µ| ≥ 2, a carcass K of µ, and nonempty nodes a ≠ b of H_µ with x ∈ α, y ∈ β; reason: the children of µ are exactly the nonempty nodes of H_µ (Theorem 2.2), so x and y lie in different children iff µ = LCA_T(x, y)
--   - reading: the list T1, …, Tk, reporting "one of the two semi-cycles" of each cycle first → every list sorted by the traversal key of some simple α–β path Q (Q runs through the semi-cycles reported first); reason: the choice of semi-cycle is arbitrary in the paper; each choice is one path Q
-- source:
--   Koustav Bhanja, Merav Parter, Asaf Petruschka, STOC 2027 submission #1544 (October 2026), Lemma 6.4, p. 21 (PDF 23)

import Mathlib
import Definitions.Def_BeyondGomoryHu_Units_Hierarchy

set_option autoImplicit false

namespace BeyondGomoryHu.Units

theorem lemma_6_4 {V : Type} [Fintype V] [DecidableEq V] (G : WGraph V) (hG : G.Connected) (μ : Finset V) (hμ : IsNode G μ) (hμ2 : 2 ≤ μ.card)
    {N : Type} [Fintype N] (K : Carcass V N) (hK : IsCarcass G μ K)
    (a b : N) (hab : a ≠ b) (x y : V) (hx : x ∈ K.terms a) (hy : y ∈ K.terms b) (L : List (Set N)) (hL : IsTraversalList K a b L) :
    L.Pairwise (fun T T' => ¬ SetPrec G x y (compTerms K T') (compTerms K T)) := by sorry

end BeyondGomoryHu.Units

-- Prove2me | Theorems.Thm_BeyondGomoryHu_Units_observation_3_2
-- name    : BeyondGomoryHu.Units.observation_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:50:17.316448+00:00
-- url     : https://prove2.me/theorems/bbdbf328-0fa2-4eab-9f0e-1cdc8bce52ad
-- title:
--   Observation 3.2 — αβ-components lie in distinct x,y-units (corrected: S-cut meets S on both sides)
-- statement:
--   Throughout, $G=(V,E,w)$ is a connected undirected graph with positive integer weights (the standing assumption of Section 2), $\mu$ is a non-leaf node of the skeleton hierarchy $\mathcal T$ and $(H_\mu,\pi_\mu)$ is a connectivity carcass of $\mu$.
--
--   Let $\mu=\mathrm{LCA}_{\mathcal T}(x,y)$ and let $\alpha\ni x$, $\beta\ni y$ be its children. Then every $\alpha\beta$-component $T$ is contained in one $x,y$-unit, and that unit contains no other $\alpha\beta$-component:
--   $$\forall s,t\in T:\ \phi_{x,y}(s)=\phi_{x,y}(t),\qquad \forall T'\neq T,\ s\in T,\ t\in T':\ \phi_{x,y}(s)\neq\phi_{x,y}(t).$$
--
--   It gives the partition of the LCA into $x,y$-units.
--
--   **Formalization Note.** The carcass is a hypothesis `IsCarcass G μ K` (the properties of Theorems 2.2–2.3); a projection is stored by its two endpoints and its nodes/edges are those of the unique proper path between them. A component is a set of nodes of $H_\mu$, identified with the set of terminals it contains (`compTerms`) when compared with vertex sets. Relations between sets use `SameUnitSets` and `SetPrec` (all pairs).
--
--   Differences from the source:
--   - correction: an S-cut is a set A with A ∩ S = ∅ and Ā ∩ S ≠ ∅ (p. 3, as printed) → an S-cut meets S on both sides: A ∩ S ≠ ∅ and Ā ∩ S ≠ ∅ (IsCut); reason: as printed, A = ∅ is an S-cut of capacity 0, so in the connected path a–b (weight 1) with S = {a,b} the only S-mincut is ∅; then no (x,y)-mincut exists and Theorem 2.2 fails; every proof (e.g. App. B, "s1 ∈ S ∩ A, s2 ∈ S ∩ Ā") uses the corrected definition
--   - encoding: G = (V, E, w) with w : E → Z+ → a finite vertex type V (Fin n in the goal) and a symmetric weight function w : V → V → ℕ, 0 meaning no edge; reason: same capacities of every vertex set: parallel edges add up and loops cross no cut
--   - generalization: the carcass of µ (the skeleton H_µ of Theorem 2.2 with the projections of Theorem 2.3) → any carcass data K satisfying IsCarcass G µ K, i.e. the properties listed in Theorems 2.2 and 2.3; reason: the paper uses only these properties ("It assumes only the preliminary tools from Section 2 as black boxes", p. 4); its carcass satisfies them, so the statement specializes to the source
--   - encoding: µ = LCA_T(x, y), with children α ∋ x and β ∋ y → a node µ of T with |µ| ≥ 2, a carcass K of µ, and nonempty nodes a ≠ b of H_µ with x ∈ α, y ∈ β; reason: the children of µ are exactly the nonempty nodes of H_µ (Theorem 2.2), so x and y lie in different children iff µ = LCA_T(x, y)
-- source:
--   Koustav Bhanja, Merav Parter, Asaf Petruschka, STOC 2027 submission #1544 (October 2026), Observation 3.2, p. 5 (PDF 7)

import Mathlib
import Definitions.Def_BeyondGomoryHu_Units_Hierarchy

set_option autoImplicit false

namespace BeyondGomoryHu.Units

theorem observation_3_2 {V : Type} [Fintype V] [DecidableEq V] (G : WGraph V) (hG : G.Connected) (μ : Finset V) (hμ : IsNode G μ) (hμ2 : 2 ≤ μ.card)
    {N : Type} [Fintype N] (K : Carcass V N) (hK : IsCarcass G μ K)
    (a b : N) (hab : a ≠ b) (x y : V) (hx : x ∈ K.terms a) (hy : y ∈ K.terms b) (T : Set N) (hT : IsABComp K a b T) :
    SameUnitSets G x y (compTerms K T) (compTerms K T) ∧
      ∀ T', IsABComp K a b T' → T' ≠ T →
        ∀ s ∈ compTerms K T, ∀ t ∈ compTerms K T', ¬ SameUnit G x y s t := by sorry

end BeyondGomoryHu.Units

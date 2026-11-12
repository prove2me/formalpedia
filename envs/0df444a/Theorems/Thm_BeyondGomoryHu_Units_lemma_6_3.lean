-- Prove2me | Theorems.Thm_BeyondGomoryHu_Units_lemma_6_3
-- name    : BeyondGomoryHu.Units.lemma_6_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:52:07.878654+00:00
-- url     : https://prove2.me/theorems/0f0291ed-c65a-4167-896f-765a2c6a753f
-- title:
--   Lemma 6.3 — directional numbering of a tree-edge (corrected: S-cut meets S on both sides)
-- statement:
--   Throughout, $G=(V,E,w)$ is a connected undirected graph with positive integer weights (the standing assumption of Section 2), $\mu$ is a non-leaf node of the skeleton hierarchy $\mathcal T$ and $(H_\mu,\pi_\mu)$ is a connectivity carcass of $\mu$.
--
--   Let $f$ be a tree-edge of $H_\mu$, $\gamma$ an endpoint of $f$, and $S$ the sub-skeleton rooted by $f$ in direction $\gamma$. There is a numbering $\sigma_{f,\gamma}:V\to[n]$ such that for all $u,v$ with $f\in\pi_\mu(u)\cap\pi_\mu(v)$:
--   1. $\sigma_{f,\gamma}(u)<\sigma_{f,\gamma}(v)$ implies a $\mu$-mincut $A$ with $A\cap\mu=S$, $u\in A$, $v\notin A$;
--   2. $$\sigma_{f,\gamma}(u)=\sigma_{f,\gamma}(v)\iff\phi_\mu(u)=\phi_\mu(v).$$
--
--   **Formalization Note.** The carcass is a hypothesis `IsCarcass G μ K` (the properties of Theorems 2.2–2.3); a projection is stored by its two endpoints and its nodes/edges are those of the unique proper path between them. A component is a set of nodes of $H_\mu$, identified with the set of terminals it contains (`compTerms`) when compared with vertex sets. Relations between sets use `SameUnitSets` and `SetPrec` (all pairs). $[n]=\{1,\dots,|V|\}$; `IsSigma` is the conjunction of the two items.
--
--   Differences from the source:
--   - correction: an S-cut is a set A with A ∩ S = ∅ and Ā ∩ S ≠ ∅ (p. 3, as printed) → an S-cut meets S on both sides: A ∩ S ≠ ∅ and Ā ∩ S ≠ ∅ (IsCut); reason: as printed, A = ∅ is an S-cut of capacity 0, so in the connected path a–b (weight 1) with S = {a,b} the only S-mincut is ∅; then no (x,y)-mincut exists and Theorem 2.2 fails; every proof (e.g. App. B, "s1 ∈ S ∩ A, s2 ∈ S ∩ Ā") uses the corrected definition
--   - encoding: G = (V, E, w) with w : E → Z+ → a finite vertex type V (Fin n in the goal) and a symmetric weight function w : V → V → ℕ, 0 meaning no edge; reason: same capacities of every vertex set: parallel edges add up and loops cross no cut
--   - generalization: the carcass of µ (the skeleton H_µ of Theorem 2.2 with the projections of Theorem 2.3) → any carcass data K satisfying IsCarcass G µ K, i.e. the properties listed in Theorems 2.2 and 2.3; reason: the paper uses only these properties ("It assumes only the preliminary tools from Section 2 as black boxes", p. 4); its carcass satisfies them, so the statement specializes to the source
-- source:
--   Koustav Bhanja, Merav Parter, Asaf Petruschka, STOC 2027 submission #1544 (October 2026), Lemma 6.3, p. 21 (PDF 23); proof in Appendix B, pp. 33–34 (PDF 35–36)

import Mathlib
import Definitions.Def_BeyondGomoryHu_Units_Hierarchy

set_option autoImplicit false

namespace BeyondGomoryHu.Units

theorem lemma_6_3 {V : Type} [Fintype V] [DecidableEq V] (G : WGraph V) (hG : G.Connected) (μ : Finset V) (hμ : IsNode G μ) (hμ2 : 2 ≤ μ.card)
    {N : Type} [Fintype N] (K : Carcass V N) (hK : IsCarcass G μ K) (c γ : N)
    (hf : IsTreeEdge K.H s(c, γ)) :
    ∃ σ : V → ℕ, (∀ v, 1 ≤ σ v ∧ σ v ≤ Fintype.card V) ∧ IsSigma G μ K c γ σ := by sorry

end BeyondGomoryHu.Units

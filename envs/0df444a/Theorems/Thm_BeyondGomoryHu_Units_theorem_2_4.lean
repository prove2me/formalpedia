-- Prove2me | Theorems.Thm_BeyondGomoryHu_Units_theorem_2_4
-- name    : BeyondGomoryHu.Units.theorem_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:49:36.354596+00:00
-- url     : https://prove2.me/theorems/7b8594fb-49b6-4470-b2c3-6d3c0f5f1bd7
-- title:
--   Theorem 2.4 — distinctness property of the carcass (corrected: S-cut meets S on both sides)
-- statement:
--   Let $G$ be a connected undirected graph with positive integer weights, $S\subseteq V$ with $|S|\ge2$, and $H_S$ a skeleton of $S$. Let $u,v\in V$ and let $C$ be a canonical cut of $H_S$ that distinguishes $u$ or $v$ (or both). If no $S$-mincut represented by $C$ separates $u$ from $v$, then
--   $$\phi_S(u)=\phi_S(v).$$
--
--   Distinctness is what lets $S$-unit identifiers decide equality of finer units; it is used at the LCA (Lemma 3.4) and in Lemma 6.3.
--
--   **Formalization Note.** The statement is made for every carcass data `K` with the skeleton properties of Theorem 2.2.
--
--   Differences from the source:
--   - correction: an S-cut is a set A with A ∩ S = ∅ and Ā ∩ S ≠ ∅ (p. 3, as printed) → an S-cut meets S on both sides: A ∩ S ≠ ∅ and Ā ∩ S ≠ ∅ (IsCut); reason: as printed, A = ∅ is an S-cut of capacity 0, so in the connected path a–b (weight 1) with S = {a,b} the only S-mincut is ∅; then no (x,y)-mincut exists and Theorem 2.2 fails; every proof (e.g. App. B, "s1 ∈ S ∩ A, s2 ∈ S ∩ Ā") uses the corrected definition
--   - correction: S ⊆ V any terminal set, with d(S) := 0 for |S| ≤ 1 → 2 ≤ |S|; reason: for |S| ≤ 1 no skeleton exists: d(S) = 0 forces every node to be empty of degree ≥ 3, such a cactus has a canonical cut, but there is no valid partition (and for S = {s} the terminal node of s required by Theorem 2.3 cannot exist); the paper applies the carcass only to non-leaf nodes of T, which have ≥ 2 vertices
--   - encoding: G = (V, E, w) with w : E → Z+ → a finite vertex type V (Fin n in the goal) and a symmetric weight function w : V → V → ℕ, 0 meaning no edge; reason: same capacities of every vertex set: parallel edges add up and loops cross no cut
--   - generalization: the skeleton H_S of Theorem 2.2 → every carcass data with the skeleton properties (IsSkeleton); reason: hypothesis and conclusion depend on C only through its valid partition, and the bijection of Theorem 2.2 makes these partitions the same for every such skeleton; the source's skeleton is one of them
-- source:
--   Koustav Bhanja, Merav Parter, Asaf Petruschka, STOC 2027 submission #1544 (October 2026), Theorem 2.4 ("Distinctness" property), p. 4 (PDF 6)

import Mathlib
import Definitions.Def_BeyondGomoryHu_Units_Hierarchy

set_option autoImplicit false

namespace BeyondGomoryHu.Units

theorem theorem_2_4 {V : Type} [Fintype V] [DecidableEq V] (G : WGraph V) (hG : G.Connected) (S : Finset V)
    (hS : 2 ≤ S.card) {N : Type} [Fintype N] (K : Carcass V N) (hK : IsSkeleton G S K)
    (u v : V) (C : Set (Sym2 N)) (hC : IsCanonicalCut K.H C)
    (hd : DistinguishedByCut G S K C u ∨ DistinguishedByCut G S K C v)
    (hns : ∀ A : Finset V, Represents G S K C A → (u ∈ A ↔ v ∈ A)) :
    SEquiv G S u v := by sorry

end BeyondGomoryHu.Units

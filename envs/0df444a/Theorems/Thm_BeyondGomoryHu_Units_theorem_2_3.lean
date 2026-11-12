-- Prove2me | Theorems.Thm_BeyondGomoryHu_Units_theorem_2_3
-- name    : BeyondGomoryHu.Units.theorem_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:49:38.599007+00:00
-- url     : https://prove2.me/theorems/18729a34-fbfd-44d3-8584-dd8597b3daee
-- title:
--   Theorem 2.3 — projections into the skeleton (corrected: S-cut meets S on both sides)
-- statement:
--   Let $G$ be a connected undirected graph with positive integer weights and $S\subseteq V$ with $|S|\ge2$. The skeleton $H_S$ of Theorem 2.2 can be chosen together with a projection $\pi_S(v)$ of every vertex $v$ such that
--   1. if $v$ is stretched, $\pi_S(v)$ is a proper path that starts and ends by tree-edges, and a canonical cut $C$ distinguishes $v$ iff $\pi_S(v)$ has endpoints on both sides of $C$ (i.e. iff $C$ contains an edge of $\pi_S(v)$);
--   2. if $v$ is not stretched, $\pi_S(v)$ is a tree-node, and for $v\in S$ it is the terminal node containing $v$;
--   3. if a canonical cut $C$ of the valid partition $S_1,S_2$ keeps $\pi_S(v)$ entirely on the side of $S_1$, then
--   $$\forall\, S\text{-mincut } A \text{ inducing } S_1,S_2:\quad v \text{ lies on the side of } A \text{ containing } S_1.$$
--
--   Together with the skeleton this is the connectivity carcass; every later statement of the mission takes such a carcass as its hypothesis.
--
--   **Formalization Note.** The conclusion is the existence of carcass data `K` with `IsCarcass G S K` (skeleton and projection properties).
--
--   Differences from the source:
--   - correction: an S-cut is a set A with A ∩ S = ∅ and Ā ∩ S ≠ ∅ (p. 3, as printed) → an S-cut meets S on both sides: A ∩ S ≠ ∅ and Ā ∩ S ≠ ∅ (IsCut); reason: as printed, A = ∅ is an S-cut of capacity 0, so in the connected path a–b (weight 1) with S = {a,b} the only S-mincut is ∅; then no (x,y)-mincut exists and Theorem 2.2 fails; every proof (e.g. App. B, "s1 ∈ S ∩ A, s2 ∈ S ∩ Ā") uses the corrected definition
--   - correction: S ⊆ V any terminal set, with d(S) := 0 for |S| ≤ 1 → 2 ≤ |S|; reason: for |S| ≤ 1 no skeleton exists: d(S) = 0 forces every node to be empty of degree ≥ 3, such a cactus has a canonical cut, but there is no valid partition (and for S = {s} the terminal node of s required by Theorem 2.3 cannot exist); the paper applies the carcass only to non-leaf nodes of T, which have ≥ 2 vertices
--   - encoding: G = (V, E, w) with w : E → Z+ → a finite vertex type V (Fin n in the goal) and a symmetric weight function w : V → V → ℕ, 0 meaning no edge; reason: same capacities of every vertex set: parallel edges add up and loops cross no cut
--   - encoding: a cactus is an undirected connected graph (Definition 2.1) → a Mathlib SimpleGraph on a finite node type (no loops or parallel edges, so every cycle has ≥ 3 nodes); reason: a 2-cycle has no two non-adjacent edges, so it gives no canonical cut, and its two incident tree-edges would represent the same valid partition, contradicting the bijection of Theorem 2.2; the source's skeleton has no 2-cycle
-- source:
--   Koustav Bhanja, Merav Parter, Asaf Petruschka, STOC 2027 submission #1544 (October 2026), Theorem 2.3 (Projections), p. 4 (PDF 6)

import Mathlib
import Definitions.Def_BeyondGomoryHu_Units_Hierarchy

set_option autoImplicit false

namespace BeyondGomoryHu.Units

theorem theorem_2_3 {V : Type} [Fintype V] [DecidableEq V] (G : WGraph V) (hG : G.Connected) (S : Finset V)
    (hS : 2 ≤ S.card) :
    ∃ (N : Type) (_ : Fintype N) (K : Carcass V N), IsCarcass G S K := by sorry

end BeyondGomoryHu.Units

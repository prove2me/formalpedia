-- Prove2me | Theorems.Thm_BeyondGomoryHu_Units_theorem_2_2
-- name    : BeyondGomoryHu.Units.theorem_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:50:00.867401+00:00
-- url     : https://prove2.me/theorems/4be24f24-3ec3-485f-a519-2d90a2191001
-- title:
--   Theorem 2.2 — skeleton of a terminal set (corrected: S-cut meets S on both sides)
-- statement:
--   Let $G=(V,E,w)$ be a connected undirected graph with positive integer weights and $S\subseteq V$ a terminal set with $|S|\ge2$. There is a universal constant $c$ such that $S$ has a **skeleton** $H_S$: a cactus whose nonempty (terminal) tree-nodes are $d(S)$ in number and represent the sets $\{S\cap U\mid U \text{ a terminal } S\text{-unit}\}$; whose further, empty nodes have degree at least $3$ (exactly $3$ for cycle-nodes) and number at most
--   $$\#\{\text{empty nodes of } H_S\}\le c\cdot d(S);$$
--   and whose canonical cuts $C$ correspond bijectively to the valid partitions $S_1,S_2$ of $S$, $S_1$ and $S_2$ being the terminals on the two sides of $C$.
--
--   The skeleton is the first half of Dinitz and Vainshtein's connectivity carcass, the representation of all Steiner mincuts of $S$ on which the whole construction rests.
--
--   **Formalization Note.** `IsSkeleton G S K` collects the listed properties; the bound $O(d(S))$ becomes one constant $c$, quantified before the graph and $S$.
--
--   Differences from the source:
--   - correction: an S-cut is a set A with A ∩ S = ∅ and Ā ∩ S ≠ ∅ (p. 3, as printed) → an S-cut meets S on both sides: A ∩ S ≠ ∅ and Ā ∩ S ≠ ∅ (IsCut); reason: as printed, A = ∅ is an S-cut of capacity 0, so in the connected path a–b (weight 1) with S = {a,b} the only S-mincut is ∅; then no (x,y)-mincut exists and Theorem 2.2 fails; every proof (e.g. App. B, "s1 ∈ S ∩ A, s2 ∈ S ∩ Ā") uses the corrected definition
--   - correction: S ⊆ V any terminal set, with d(S) := 0 for |S| ≤ 1 → 2 ≤ |S|; reason: for |S| ≤ 1 no skeleton exists: d(S) = 0 forces every node to be empty of degree ≥ 3, such a cactus has a canonical cut, but there is no valid partition (and for S = {s} the terminal node of s required by Theorem 2.3 cannot exist); the paper applies the carcass only to non-leaf nodes of T, which have ≥ 2 vertices
--   - encoding: G = (V, E, w) with w : E → Z+ → a finite vertex type V (Fin n in the goal) and a symmetric weight function w : V → V → ℕ, 0 meaning no edge; reason: same capacities of every vertex set: parallel edges add up and loops cross no cut
--   - encoding: O(d(S)) empty nodes → ∃ c (before V, G, S), #empty nodes ≤ c · d(S); reason: one universal constant for the O(·)
--   - encoding: a cactus is an undirected connected graph (Definition 2.1) → a Mathlib SimpleGraph on a finite node type (no loops or parallel edges, so every cycle has ≥ 3 nodes); reason: a 2-cycle has no two non-adjacent edges, so it gives no canonical cut, and its two incident tree-edges would represent the same valid partition, contradicting the bijection of Theorem 2.2; the source's skeleton has no 2-cycle
-- source:
--   Koustav Bhanja, Merav Parter, Asaf Petruschka, STOC 2027 submission #1544 (October 2026), Theorem 2.2 (Skeleton), p. 3 (PDF 5), cited from [DV94, DV95, DV00]

import Mathlib
import Definitions.Def_BeyondGomoryHu_Units_Hierarchy

set_option autoImplicit false

namespace BeyondGomoryHu.Units

theorem theorem_2_2 :
    ∃ c : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : WGraph V), G.Connected →
      ∀ S : Finset V, 2 ≤ S.card →
        ∃ (N : Type) (_ : Fintype N) (K : Carcass V N), IsSkeleton G S K ∧
          (Finset.univ.filter (fun c => K.terms c = ∅)).card ≤ c * dS G S := by sorry

end BeyondGomoryHu.Units

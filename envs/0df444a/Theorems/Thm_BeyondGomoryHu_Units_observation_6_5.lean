-- Prove2me | Theorems.Thm_BeyondGomoryHu_Units_observation_6_5
-- name    : BeyondGomoryHu.Units.observation_6_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:52:11.641195+00:00
-- url     : https://prove2.me/theorems/760bae88-4b39-4822-ac87-a0d5c4bb524c
-- title:
--   Observation 6.5 — the cuts C_j and the rightmost component (corrected: S-cut meets S on both sides)
-- statement:
--   Throughout, $G=(V,E,w)$ is a connected undirected graph with positive integer weights (the standing assumption of Section 2), $\mu$ is a non-leaf node of the skeleton hierarchy $\mathcal T$ and $(H_\mu,\pi_\mu)$ is a connectivity carcass of $\mu$.
--
--   Let $\mu=\mathrm{LCA}_{\mathcal T}(x,y)$, $T_1,\dots,T_k$ the traversal list of Lemma 6.4, and for $1<j\le k$ let $C_j$ be the canonical cut of the valid partition of $\mu$ into $T_1\cup\dots\cup T_{j-1}$ (containing $\alpha\ni x$) and $T_j\cup\dots\cup T_k$ (containing $\beta\ni y$). Let $v$ be a split vertex (its projection is in no single $\alpha\beta$-component) with rightmost component $T_r(v)=T_i$. Then
--   1. $C_i$ distinguishes $v$;
--   2. whenever $j>i$, $C_j$ keeps all of $\pi_\mu(v)$ on the side of $\alpha$.
--
--   **Formalization Note.** The carcass is a hypothesis `IsCarcass G μ K` (the properties of Theorems 2.2–2.3); a projection is stored by its two endpoints and its nodes/edges are those of the unique proper path between them. A component is a set of nodes of $H_\mu$, identified with the set of terminals it contains (`compTerms`) when compared with vertex sets. Relations between sets use `SameUnitSets` and `SetPrec` (all pairs). List indices are 0-based in Lean: the 1-based $C_j$ has $\alpha$-side terminals `prefixTerms K L (j-1)`. The existence of $C_j$ (validity of the prefix partition), which the observation presupposes, is stated as the first conjunct.
--
--   Differences from the source:
--   - correction: an S-cut is a set A with A ∩ S = ∅ and Ā ∩ S ≠ ∅ (p. 3, as printed) → an S-cut meets S on both sides: A ∩ S ≠ ∅ and Ā ∩ S ≠ ∅ (IsCut); reason: as printed, A = ∅ is an S-cut of capacity 0, so in the connected path a–b (weight 1) with S = {a,b} the only S-mincut is ∅; then no (x,y)-mincut exists and Theorem 2.2 fails; every proof (e.g. App. B, "s1 ∈ S ∩ A, s2 ∈ S ∩ Ā") uses the corrected definition
--   - encoding: G = (V, E, w) with w : E → Z+ → a finite vertex type V (Fin n in the goal) and a symmetric weight function w : V → V → ℕ, 0 meaning no edge; reason: same capacities of every vertex set: parallel edges add up and loops cross no cut
--   - generalization: the carcass of µ (the skeleton H_µ of Theorem 2.2 with the projections of Theorem 2.3) → any carcass data K satisfying IsCarcass G µ K, i.e. the properties listed in Theorems 2.2 and 2.3; reason: the paper uses only these properties ("It assumes only the preliminary tools from Section 2 as black boxes", p. 4); its carcass satisfies them, so the statement specializes to the source
--   - encoding: µ = LCA_T(x, y), with children α ∋ x and β ∋ y → a node µ of T with |µ| ≥ 2, a carcass K of µ, and nonempty nodes a ≠ b of H_µ with x ∈ α, y ∈ β; reason: the children of µ are exactly the nonempty nodes of H_µ (Theorem 2.2), so x and y lie in different children iff µ = LCA_T(x, y)
--   - reading: "let C_j be the canonical cut corresponding to the valid partition …" (1 < j ≤ k) → existence of a canonical cut with that α-side for each prefix, and the two bullets for every canonical cut with that α-side; reason: the sentence presupposes that the prefix partitions are valid; their canonical cut is unique by Theorem 2.2
-- source:
--   Koustav Bhanja, Merav Parter, Asaf Petruschka, STOC 2027 submission #1544 (October 2026), Observation 6.5, p. 22 (PDF 24)

import Mathlib
import Definitions.Def_BeyondGomoryHu_Units_Hierarchy

set_option autoImplicit false

namespace BeyondGomoryHu.Units

theorem observation_6_5 {V : Type} [Fintype V] [DecidableEq V] (G : WGraph V) (hG : G.Connected) (μ : Finset V) (hμ : IsNode G μ) (hμ2 : 2 ≤ μ.card)
    {N : Type} [Fintype N] (K : Carcass V N) (hK : IsCarcass G μ K)
    (a b : N) (hab : a ≠ b) (x y : V) (hx : x ∈ K.terms a) (hy : y ∈ K.terms b) (L : List (Set N)) (hL : IsTraversalList K a b L)
    (v : V) (hsplit : ¬ ∃ T, IsABComp K a b T ∧ projNodes K v ⊆ T) (i : ℕ) (hi : i < L.length)
    (hr : IsRightmost K a b L v L[i]) :
    (∀ j, 1 ≤ j → j < L.length →
      ∃ C, IsCanonicalCut K.H C ∧ sideTerms K C a = prefixTerms K L j) ∧
    (∀ C, IsCanonicalCut K.H C → sideTerms K C a = prefixTerms K L i →
      DistinguishedByCut G μ K C v) ∧
    (∀ j, i < j → j < L.length → ∀ C, IsCanonicalCut K.H C →
      sideTerms K C a = prefixTerms K L j → ∀ d ∈ projNodes K v, SameSide K.H C a d) := by sorry

end BeyondGomoryHu.Units

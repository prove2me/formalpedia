-- Prove2me | Theorems.Thm_EdgeSublinearMWIS_Main_lemma_14
-- name    : EdgeSublinearMWIS.Main.lemma_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T13:45:04.148376+00:00
-- url     : https://prove2.me/theorems/6c483d5a-b949-4405-a90c-e322c360c7c9
-- title:
--   Lemma 14 — termination and the full Solve invariant
-- statement:
--   Fix the promised hereditary class and its integer exponent $a\ge2$ and treewidth constant. There are fixed finite implementations of the source's separator and exact rational feasibility routines, and a fixed positive threshold coefficient, for which every operational Solve call on an induced input terminates. All returned pairs $(I_G,u_G)$ satisfy
--   $$I_G\text{ independent},\quad\alpha(G)\le u_G\le|V(G)|,\quad |I_G|\ge(1-\delta)^{h(|V(G)|)}u_G.$$
--   The integer $u_G$ is the first successful target in the actual descending loop. The parameters are fixed from the original input throughout recursion. Correct primitive behavior is a conclusion, not an additional input assumption. Empty and singleton inputs use the direct edgeless branch. This is the recursive invariant required for both the accuracy and runtime results.
--
--   Differences from the source:
--   - encoding: arbitrary finite simple graphs → graphs labeled by Fin n and finite vertex masks; reason: every finite graph admits such a labeling; induced injections transport class membership
--   - encoding: Algorithms 1–2 with correct separator and exact rational feasibility implementations → raw finite subprograms and their correctness as existential conclusions, plus the explicit Execute relation; reason: the operational definition supplies all control flow; termination and invariant are proved properties, not constructor assumptions
--   - encoding: an unspecified class-uniform threshold p=O_C((delta inverse log n)^(4a-2)), nondecreasing in n → max(1,ceil(B (h(n)/delta)^(4a-2))) for one positive integer B before all inputs; reason: p may be enlarged by the p.11 monotonicity argument; h(n) is within universal constant factors of log_2 n
--   - encoding: every call terminates → a finite operational execution exists, and every result obeys all clauses of (23); reason: the raw programs and fixed control flow are deterministic; the result type itself carries no invariant
-- source:
--   Édouard Bonnet, Yeonsu Chang, STOC 2027 submission #1044 (October 2026), Lemma 14, Eq. (23), Algorithms 1–2, p.18 (PDF p.18), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1044.pdf

import Definitions.Def_EdgeSublinearMWIS_Main_AlgorithmContracts

namespace EdgeSublinearMWIS.Main

/-- Correct implementations are conclusions. Solve is the operational recursion,
not an optimizer or a value satisfying an invariant by construction. -/
theorem lemma_14 (C : GraphClass) (a : ℕ) (K : ℝ)
    (separatorClass : StronglyEdgeSublinear C) (ha : 2 ≤ a) (bound : TreewidthBound C a K) :
    ∃ (B : ℕ) (M : Routines), 0 < B ∧ PrimitiveContract C a B M ∧ SolveInvariant C a B M := by sorry

end EdgeSublinearMWIS.Main

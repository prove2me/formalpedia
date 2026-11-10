-- Prove2me | Theorems.Thm_EdgeSublinearMWIS_Main_corollary_15
-- name    : EdgeSublinearMWIS.Main.corollary_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T13:45:33.366196+00:00
-- url     : https://prove2.me/theorems/72414711-7537-4d82-8fa5-645788cbab42
-- title:
--   Corollary 15 — unweighted approximation from the actual Solve
-- statement:
--   For the fixed promised class there are fixed finite subprogram implementations and a threshold coefficient for the same operational Algorithms 1–2. For every member $G$ and every rational $0<\varepsilon<1$, Solve with the source's shared parameters returns an independent set $I_G$ with
--   $$|I_G|\ge(1-\varepsilon)\alpha(G).$$
--   Its primitive correctness and the full recursive invariant are also conclusions. The domain includes empty, singleton and edgeless graphs, which use the direct branch. This is the unweighted accuracy guarantee used by the weighted reduction.
--
--   Differences from the source:
--   - encoding: arbitrary finite simple graphs → graphs labeled by Fin n and finite vertex masks; reason: every finite graph admits such a labeling; induced injections transport class membership
--   - encoding: Algorithms 1–2 with correct separator and exact rational feasibility implementations → raw finite subprograms and their correctness as existential conclusions, plus the explicit Execute relation; reason: the operational definition supplies all control flow; termination and invariant are proved properties, not constructor assumptions
--   - encoding: an unspecified class-uniform threshold p=O_C((delta inverse log n)^(4a-2)), nondecreasing in n → max(1,ceil(B (h(n)/delta)^(4a-2))) for one positive integer B before all inputs; reason: p may be enlarged by the p.11 monotonicity argument; h(n) is within universal constant factors of log_2 n
-- source:
--   Édouard Bonnet, Yeonsu Chang, STOC 2027 submission #1044 (October 2026), Corollary 15, Eq. (22), p.18 (PDF p.18), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1044.pdf

import Definitions.Def_EdgeSublinearMWIS_Main_AlgorithmContracts

namespace EdgeSublinearMWIS.Main

theorem corollary_15 (C : GraphClass) (a : ℕ) (K : ℝ)
    (separatorClass : StronglyEdgeSublinear C) (ha : 2 ≤ a) (bound : TreewidthBound C a K) :
    ∃ (B : ℕ) (M : Routines), 0 < B ∧ PrimitiveContract C a B M ∧ SolveInvariant C a B M ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (ε : ℚ),
        C n G → 0 < ε → ε < 1 →
        ∃ (I : Finset (Fin n)) (u : ℕ),
          Execute G (parameters B a n ε) M (.solve Finset.univ) (.solved I u) ∧
          G.IsIndepSet (I : Set (Fin n)) ∧
          (1 - (ε : ℝ)) * alpha G Finset.univ ≤ (I.card : ℝ) := by sorry

end EdgeSublinearMWIS.Main

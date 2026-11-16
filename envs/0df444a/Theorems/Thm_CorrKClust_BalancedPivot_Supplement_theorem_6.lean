-- Prove2me | Theorems.Thm_CorrKClust_BalancedPivot_Supplement_theorem_6
-- name    : CorrKClust.BalancedPivot.Supplement.theorem_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:31:18.63205+00:00
-- url     : https://prove2.me/theorems/a2ee6cdc-2a05-43a3-937b-8802f717dce8
-- title:
--   Theorem 6 — strong NP-hardness on disjoint cliques
-- statement:
--   The threshold decision problem for disjoint-clique correlation $k$-clustering is NP-hard under polynomial-time many-one reductions. This holds both with binary numerical parameters and with unary $k,T$, the latter expressing strong NP-hardness. The target admits every clustering into at most $k$ labels, including those splitting original cliques:
--   $$L=\{(G,k,T):G\text{ is a union of disjoint cliques},\ k\ge1,\ \exists f:V\to\{0,\ldots,k-1\},\ \operatorname{Cost}_G(f)\le T\}.$$
--   The explicit transformation from the existing unary indexed 3-PARTITION language is polynomial time and preserves membership on every string. For each valid positive source instance with $3m$ entries $a_i$, target $B$, and sum $mB$, the constructed graph has $mB$ actual vertices, $k=m$, and an integral nonnegative threshold satisfying
--   $$2T+\sum_i a_i^2=mB^2.$$
--   The source has a solution if and only if some arbitrary target clustering costs at most $T$. The theorem asserts hardness itself; source hardness is not assumed as a hypothesis. It therefore establishes hardness of computing an optimum as well.
--
--   Differences from the source:
--   - encoding: strong NP-hardness of the optimization problem → NP-hardness of explicit adjacency-matrix threshold languages with binary and unary k,T, plus the paper reduction and its exact threshold identity; reason: a computed optimum decides these languages; unary numerical parameters express the strong version, and the reduction permits all target clusterings
--   - encoding: positive 3-PARTITION instances in the reduction → the published indexed unary source language, with empty valid instances sent to a fixed YES-instance and non-codes to a fixed NO-instance; reason: positive instances use precisely the paper construction; total handling of degenerate source strings makes a valid many-one reduction without adding a source-hardness hypothesis
-- source:
--   Mahsa Derakhshan, Andisheh Ghasemi, Rajmohan Rajaraman, Omer Wasim, Tegan Wilson, STOC 2027 submission #302 (October 2026), Theorem 6, p. 47

import Definitions.Def_CorrKClust_BalancedPivot_Supplement_Offline

set_option autoImplicit false
open Classical
noncomputable section

namespace CorrKClust.BalancedPivot.Supplement

/-- Theorem 6, printed p.47: actual NP-hardness for both encodings. Hardness with
unary numerical parameters is the strong version, not a hypothesis on the source problem.
The source language is reused, including its empty YES-instances. -/
theorem theorem_6 :
    KingTerrain.NPHard.IsNPHard (decisionLanguage true) ∧
    KingTerrain.NPHard.IsNPHard (decisionLanguage false) ∧
    CookPvsNP.PolyTimeComputable sourceReduction ∧
    (∀ w, w ∈ TetrisHard.Rows.threePartitionLanguage ↔ sourceReduction w ∈ decisionLanguage true) ∧
    (∀ P : TetrisHard.Rows.ThreePartition, P.Valid → 0 < P.s →
      Fintype.card (ReductionVertex P) = P.s * P.target ∧
      2 * reductionThreshold P + (∑ i, (P.entry i) ^ 2) = P.s * P.target ^ 2 ∧
      (P.HasSolution ↔ ∃ f : Fin (Fintype.card (ReductionVertex P)) → Fin P.s,
        cost (reductionGraph P) f ≤ reductionThreshold P)) := by sorry

end CorrKClust.BalancedPivot.Supplement

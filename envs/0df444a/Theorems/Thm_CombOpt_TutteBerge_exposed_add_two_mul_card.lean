-- Prove2me | Theorems.Thm_CombOpt_TutteBerge_exposed_add_two_mul_card
-- name    : CombOpt.TutteBerge.exposed_add_two_mul_card
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:06:04.439963+00:00
-- url     : https://prove2.me/theorems/17e4da4d-a2e1-4b0a-aba3-13f36adc1d1c
-- title:
--   §5.1, p. 127 — a matching covers $2|M|$ nodes and leaves $|V|-2|M|$ exposed
-- statement:
--   Let $M$ be a matching of a finite graph $G=(V,E)$. Then the number of nodes covered by $M$ is exactly $2|M|$, and the number of $M$-exposed nodes is $|V|-2|M|$.
--
--   The second count is the bookkeeping that turns statements about exposed nodes into statements about matching sizes.
--
--   Differences from the source:
--   - reading: a matching is a set of edges such that no node is incident with more than one of them (p. 127) → IsMatching also requires that no edge of M is a loop; reason: the book's next sentences say M covers exactly 2|M| nodes and leaves |V| − 2|M| exposed, which fails for a loop
--   - encoding: |V|, |M|, |A| for finite sets → Nat.card V and Set.ncard, with binders [Finite V] [Finite E]; reason: these are the true cardinalities of finite sets
--   - encoding: number of exposed nodes = |V| − 2|M| → (exposed count) + 2|M| = |V|; reason: avoids truncated subtraction in ℕ; equivalent
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §5.1, p. 127 (PDF p. 135)

import Mathlib
import Definitions.Def_CombOpt_TutteBerge_Multigraph
import Definitions.Def_CombOpt_TutteBerge_Multigraph_Covers
import Definitions.Def_CombOpt_TutteBerge_Multigraph_exposedNodes
import Definitions.Def_CombOpt_TutteBerge_Multigraph_IsMatching

namespace CombOpt.TutteBerge

/-- Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §5.1, p. 127 (PDF p. 135): "the number of nodes covered by M is exactly 2|M|, and that
the number of M-exposed nodes is |V| − 2|M|."

The second count is written `|exposed| + 2|M| = |V|` to avoid truncated subtraction. -/
theorem exposed_add_two_mul_card {V E : Type*} [Finite V] [Finite E] (G : Multigraph V E)
    (M : Set E) (hM : G.IsMatching M) :
    {v : V | G.Covers M v}.ncard = 2 * M.ncard ∧
      (G.exposedNodes M).ncard + 2 * M.ncard = Nat.card V := by sorry

end CombOpt.TutteBerge

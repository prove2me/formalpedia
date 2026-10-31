-- Prove2me | Theorems.Thm_CombOpt_TutteBerge_deficiency_add_two_mul_matchingNumber
-- name    : CombOpt.TutteBerge.deficiency_add_two_mul_matchingNumber
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:07:24.066756+00:00
-- url     : https://prove2.me/theorems/58d87285-04f2-4141-bbf9-cfcc6f8701e4
-- title:
--   §5.1, p. 127 — $\mathrm{def}(G)=|V|-2\nu(G)$
-- statement:
--   For a finite graph $G=(V,E)$,
--   $$
--   \mathrm{def}(G)=|V|-2\nu(G).
--   $$
--   So a matching is maximum exactly when it leaves the fewest nodes exposed, and bounds on $\nu$ and on $\mathrm{def}$ are interchangeable.
--
--   Differences from the source:
--   - reading: a matching is a set of edges such that no node is incident with more than one of them (p. 127) → IsMatching also requires that no edge of M is a loop; reason: the book's next sentences say M covers exactly 2|M| nodes and leaves |V| − 2|M| exposed, which fails for a loop
--   - encoding: |V|, |M|, |A| for finite sets → Nat.card V and Set.ncard, with binders [Finite V] [Finite E]; reason: these are the true cardinalities of finite sets
--   - encoding: def(G) = |V| − 2ν(G) → def(G) + 2ν(G) = |V|; reason: avoids truncated subtraction in ℕ; equivalent
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §5.1, p. 127 (PDF p. 135)

import Mathlib
import Definitions.Def_CombOpt_TutteBerge_Multigraph
import Definitions.Def_CombOpt_TutteBerge_Multigraph_deficiency
import Definitions.Def_CombOpt_TutteBerge_Multigraph_matchingNumber

namespace CombOpt.TutteBerge

/-- Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §5.1, p. 127 (PDF p. 135): "So def(G) = |V| − 2ν(G)."

Written `def(G) + 2ν(G) = |V|` to avoid truncated subtraction. -/
theorem deficiency_add_two_mul_matchingNumber {V E : Type*} [Finite V] [Finite E]
    (G : Multigraph V E) : G.deficiency + 2 * G.matchingNumber = Nat.card V := by sorry

end CombOpt.TutteBerge

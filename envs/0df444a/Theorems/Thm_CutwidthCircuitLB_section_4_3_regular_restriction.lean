-- Prove2me | Theorems.Thm_CutwidthCircuitLB_section_4_3_regular_restriction
-- name    : CutwidthCircuitLB.section_4_3_regular_restriction
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:27:51.15967+00:00
-- url     : https://prove2.me/theorems/b0456659-f727-4d90-a41c-c31ca1cc71bc
-- title:
--   Section 4.3 — the cubic cutwidth constant is unchanged on simple 3-regular graphs
-- statement:
--   The cubic cutwidth constant is unchanged if its definition is restricted to simple 3-regular graphs: for every real $a$,
--   $$
--   \alpha \le a \iff \alpha_{3\text{-reg}} \le a ,
--   $$
--   where $\alpha$ is defined over connected loopless subcubic multigraphs and $\alpha_{3\text{-reg}}$ over connected simple 3-regular graphs, both with bounds of the form $\beta(M - N) + r(N)$, $r = o(N)$.
--
--   The compress-and-expand argument of Lemma 4.5 (contract to a simple 3-regular kernel on $h \le 2(M-N)$ vertices, order it, expand at a cost of $3\lceil \log_2 N\rceil$ edges per cut) does not depend on the constant; this is the reason for the constant's name, and it reduces Theorem 4.6 to simple 3-regular graphs.
--
--   Differences from the source:
--   - reading: the cubic cutwidth constant is unchanged if its definition is restricted to simple 3-regular graphs → ∀ a, CubicCutwidthAtMost a ↔ CubicCutwidthAtMost3Reg a, the restricted class being connected simple 3-regular graphs; reason: two constants are equal iff they have the same upper bounds; restricting the definition's class keeps its connectedness
--   - reading: the cubic cutwidth constant (an infimum over admissible β > 0) is at most α → CubicCutwidthAtMost α: every β > α admits r = o(N) with cw ≤ β(M − N) + r(N); reason: the admissible set is upward closed (M − N ≥ −1 for connected graphs), so this is equivalent to the infimum being at most α; r(N) < o(N) read as r = o(N)
-- source:
--   McGuire–Schlesinger–Williams, Explicit functions requiring larger than 4.5n size circuits, STOC 2027 submission (manuscript sha256 ed87148f…cfa3), Section 4.3, p.13 (last paragraph of the proof of Lemma 4.5)

import Mathlib
import Definitions.Def_CombOpt_MatchingPolytope_Graph
import Definitions.Def_CombOpt_MatchingPolytope_Graph_IsLoopless
import Definitions.Def_CutwidthCircuitLB_IsSubcubic
import Definitions.Def_CutwidthCircuitLB_IsConnected
import Definitions.Def_CutwidthCircuitLB_edgeMultiset
import Definitions.Def_CutwidthCircuitLB_cutSize
import Definitions.Def_CutwidthCircuitLB_CutwidthLE
import Definitions.Def_CutwidthCircuitLB_CubicCutwidthAtMost
import Definitions.Def_CutwidthCircuitLB_CubicCutwidthAtMost3Reg

namespace CutwidthCircuitLB

/-- **Section 4.3, restriction to simple 3-regular graphs** (McGuire–Schlesinger–Williams, *Explicit functions requiring larger than 4.5n size circuits*, STOC 2027 submission manuscript (sha256 ed87148f…cfa3), §4.3, p.13, last paragraph of
the proof of Lemma 4.5): the cubic cutwidth constant is unchanged if its definition is restricted
to simple 3-regular graphs: for every real `a`, it is at most `a` iff its restriction to connected
simple 3-regular graphs is at most `a`. -/
theorem section_4_3_regular_restriction (a : ℝ) :
    CubicCutwidthAtMost a ↔ CubicCutwidthAtMost3Reg a := by sorry

end CutwidthCircuitLB

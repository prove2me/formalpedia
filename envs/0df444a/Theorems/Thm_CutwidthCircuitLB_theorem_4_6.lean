-- Prove2me | Theorems.Thm_CutwidthCircuitLB_theorem_4_6
-- name    : CutwidthCircuitLB.theorem_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:27:43.918917+00:00
-- url     : https://prove2.me/theorems/3584c4e7-3920-4694-832a-3cb8eafa0e41
-- title:
--   Theorem 4.6 — the cubic cutwidth constant is at most $2\kappa_E = 0.28070\ldots$
-- statement:
--   The cubic cutwidth constant $\alpha$ satisfies
--   $$
--   \alpha \le 2\kappa_E = 0.28070\ldots, \qquad \kappa_E = \frac{3}{2\pi}\arccos\frac{1+2\sqrt2}{4}.
--   $$
--
--   With Theorem 4.3 this yields circuit lower bounds of $(1 + 1/(2\kappa_E) - \varepsilon) n$ gates; the paper reports that this bound has been verified in Lean 4 in the authors' own development.
--
--   Differences from the source:
--   - reading: the cubic cutwidth constant (an infimum over admissible β > 0) is at most α → CubicCutwidthAtMost α: every β > α admits r = o(N) with cw ≤ β(M − N) + r(N); reason: the admissible set is upward closed (M − N ≥ −1 for connected graphs), so this is equivalent to the infimum being at most α; r(N) < o(N) read as r = o(N)
--   - reading: 2κ_E = 0.28070 . . . → 0.28070 ≤ 2κ_E < 0.28071; reason: the printed digits are a truncated decimal of 0.2807019…
-- source:
--   McGuire–Schlesinger–Williams, Explicit functions requiring larger than 4.5n size circuits, STOC 2027 submission (manuscript sha256 ed87148f…cfa3), Theorem 4.6, p.14

import Mathlib
import Definitions.Def_CombOpt_MatchingPolytope_Graph
import Definitions.Def_CombOpt_MatchingPolytope_Graph_IsLoopless
import Definitions.Def_CutwidthCircuitLB_IsSubcubic
import Definitions.Def_CutwidthCircuitLB_IsConnected
import Definitions.Def_CutwidthCircuitLB_edgeMultiset
import Definitions.Def_CutwidthCircuitLB_cutSize
import Definitions.Def_CutwidthCircuitLB_CutwidthLE
import Definitions.Def_CutwidthCircuitLB_CubicCutwidthAtMost
import Definitions.Def_CutwidthCircuitLB_kappaE

namespace CutwidthCircuitLB

/-- **Theorem 4.6 (Lean-Verified Cutwidth Bound)** (McGuire–Schlesinger–Williams, *Explicit functions requiring larger than 4.5n size circuits*, STOC 2027 submission manuscript (sha256 ed87148f…cfa3), Theorem 4.6, p.14): the cubic cutwidth
constant `α` is at most `2κ_E = 0.28070…`, where `κ_E = (3/(2π)) arccos((1 + 2√2)/4)`.

**Formalization Note** "`= 0.28070…`" is the clause `0.28070 ≤ 2κ_E < 0.28071` (the value is
`0.2807019…`). -/
theorem theorem_4_6 :
    CubicCutwidthAtMost (2 * kappaE) ∧ (0.28070 : ℝ) ≤ 2 * kappaE ∧
      2 * kappaE < (0.28071 : ℝ) := by sorry

end CutwidthCircuitLB

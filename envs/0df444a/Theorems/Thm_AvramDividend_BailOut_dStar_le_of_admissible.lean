-- Prove2me | Theorems.Thm_AvramDividend_BailOut_dStar_le_of_admissible
-- name    : AvramDividend.BailOut.dStar_le_of_admissible
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-28T01:45:49.328814+00:00
-- url     : https://prove2.me/theorems/7d1143f0-41d0-4204-bda7-53f9e82fdef2
-- title:
--   The defining property of d*: every admissible a with G(a) <= 0 lies at or above d*
-- statement:
--   Let $d^* = \inf\{a>0 : G(a) \le 0\}$ be the barrier level (5.6), with
--   $G(a) = [\varphi Z^{(q)}(a)-1]W^{(q)\prime}(a) - \varphi q W^{(q)}(a)^2$.
--   Then every $a>0$ with $G(a) \le 0$ satisfies $d^* \le a$.
--
--   This is an order-theoretic consequence of the definition of $d^*$ as an infimum and uses no property of the scale function, of the triplet, or of the process. It supplies the direction in which the set defining $d^*$ lies relative to its infimum, which is the step that turns "$G$ is nonpositive somewhere above $d^*$" into "$G$ is strictly positive strictly above $d^*$" by contraposition. That sign is what makes $a \mapsto \bar v_a(x)$ nonincreasing beyond $d^*$ in the proof of Proposition 3(ii).
--
--   **Formalization Note** $G$ is `Gfun q φ W` and $d^*$ is `dStar q φ W : ℝ≥0∞` from `Definitions.Def_AvramDividend_BailOut_BarrierCandidates`. The hypotheses `0 < a` and `Gfun q φ W a ≤ 0` are exactly the two predicates bound by the infimum, and the conclusion compares the real part of `dStar` with `a`.
-- source:
--   Avram, Palmowski, Pistorius, arXiv:math/0702893v1, p. 15: sign step in the proof of Proposition 3(ii)

import Mathlib
import Definitions.Def_AvramDividend_BailOut_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_BailOut_ScaleFunction
import Definitions.Def_AvramDividend_BailOut_BarrierCandidates

open MeasureTheory
open scoped NNReal ENNReal

namespace AvramDividend.BailOut

/-- The defining property of the barrier level: every admissible barrier `a` with
`Gfun q φ W a ≤ 0` lies at or above `d*`.  Purely order-theoretic: it uses no
property of the scale function, of the triplet, or of the process. -/
theorem dStar_le_of_admissible {q φ : ℝ} {W : ℝ → ℝ} {a : ℝ}
    (ha : 0 < a) (hG : Gfun q φ W a ≤ 0) :
    (dStar q φ W).toReal ≤ a := by sorry

end AvramDividend.BailOut

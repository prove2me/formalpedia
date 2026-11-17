-- Prove2me | Theorems.Thm_EuclidSPAgg_Supplement_theorem_B_1
-- name    : EuclidSPAgg.Supplement.theorem_B_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:48:08.246323+00:00
-- url     : https://prove2.me/theorems/f175d01f-2332-45c2-8ab7-5789467b2ff5
-- title:
--   Theorem B.1 — binary strategyproof rules with convex range are projections and $\ell_1$-Lipschitz
-- statement:
--   Let $E=\mathbb R^d$ with $d\ge1$, and let $h:E^2\to E$ be deterministic and strategyproof in both arguments. Suppose its full range $C=h(E^2)$ is convex. Then:
--
--   1. every unilateral menu $\{h(a,b):a\in E\}$ and $\{h(a,b):b\in E\}$ is closed and convex;
--   2. the response of each agent is the Euclidean projection onto its menu: $h(a,b)$ is the unique nearest point to $a$ of $\{h(a',b):a'\in E\}$, and symmetrically for the second agent;
--   3. for all $a,a',b,b'\in E$,
--   $$
--   \|h(a,b)-h(a',b')\|\le\|a-a'\|+\|b-b'\| .
--   $$
--
--   This is the induction step behind the regularity of all strategyproof mechanisms with convex range (Theorem B.4) and hence behind the automatic continuity theorem (Theorem 7.1).
--
--   Differences from the source:
--   - encoding: "its response is Euclidean projection onto that menu" → the set of nearest points of the menu to the report is exactly the singleton of the outcome; reason: this is the definition of the metric projection onto a set with a unique nearest point.
-- source:
--   Jia, Strategyproof Aggregation in Euclidean Spaces: Rigidity and Median Optimality, arXiv:2609.19394 (held version, sha256 891e6125…), Theorem B.1, p.42 (PDF p.44)

import Mathlib
import Definitions.Def_EuclidSPAgg_IsStrategyproof
import Definitions.Def_EuclidSPAgg_menu
import Definitions.Def_SuperPolyak_solutionSet
open RBMSensitivity (E)

namespace EuclidSPAgg.Supplement

open EuclidSPAgg

/-- **Theorem B.1** (binary regularity; Jia, *Strategyproof Aggregation in Euclidean Spaces: Rigidity and Median Optimality*, arXiv:2609.19394 (held version, sha256 891e6125…), p.42 (PDF p.44)). Let `h : E² → E` be deterministic
and strategyproof in both arguments, and suppose its full range `C = h(E²)` is convex. Then every
unilateral menu is closed and convex, its response is Euclidean projection onto that menu, and
`‖h(a, b) − h(a′, b′)‖ ≤ ‖a − a′‖ + ‖b − b′‖` for all `a, a′, b, b′ ∈ E`.

**Formalization Note** `h : Mech 2 d`; "strategyproof in both arguments" is the published
`IsStrategyproof` on two agents. The unilateral menu of agent `i` against `x` is the published
`menu h i x`. "The response is Euclidean projection onto the menu" is: the set of nearest points of
the menu to `a` (the published `SuperPolyak.nearestPoints`) is exactly `{h(a, x₋ᵢ)}`. `h(a, b)` is
`h ![a, b]`. `d ≥ 1` is the paper's standing assumption (p.8). -/
theorem theorem_B_1 (d : ℕ) (hd : 1 ≤ d) (h : Mech 2 d) (hSP : IsStrategyproof h)
    (hconv : Convex ℝ (Set.range h)) :
    (∀ (i : Fin 2) (x : Fin 2 → E d), IsClosed (menu h i x) ∧ Convex ℝ (menu h i x) ∧
        ∀ a : E d, SuperPolyak.nearestPoints (menu h i x) a = {h (Function.update x i a)}) ∧
      ∀ a a' b b' : E d, ‖h ![a, b] - h ![a', b']‖ ≤ ‖a - a'‖ + ‖b - b'‖ := by sorry

end EuclidSPAgg.Supplement

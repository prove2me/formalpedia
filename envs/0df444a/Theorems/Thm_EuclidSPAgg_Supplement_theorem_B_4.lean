-- Prove2me | Theorems.Thm_EuclidSPAgg_Supplement_theorem_B_4
-- name    : EuclidSPAgg.Supplement.theorem_B_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:48:32.574569+00:00
-- url     : https://prove2.me/theorems/25111538-3ce8-4172-984f-6550f12a1f8f
-- title:
--   Theorem B.4 — strategyproof mechanisms with convex range are projections and $\ell_1$-Lipschitz
-- statement:
--   Let $E=\mathbb R^d$ with $d\ge1$, let $n\ge1$, and let $f:E^n\to E$ be deterministic and strategyproof, with convex full range $f(E^n)$. Then:
--
--   1. every unilateral menu $M_i(x_{-i})=\{f(a,x_{-i}):a\in E\}$ is closed and convex;
--   2. every unilateral response is the metric projection onto its menu: $f(a,x_{-i})$ is the unique nearest point of $M_i(x_{-i})$ to $a$;
--   3. for all profiles $x,x'\in E^n$,
--   $$
--   \|f(x)-f(x')\|\le\sum_{i=1}^n\|x_i-x'_i\| .
--   $$
--
--   This is the regularity theorem that proves the converse direction of Theorem 7.1 (convex range implies continuity).
--
--   Differences from the source:
--   - encoding: "every unilateral response is its metric projection" → the set of nearest points of the menu to the report is exactly the singleton of the outcome; reason: this is the definition of the metric projection onto a set with a unique nearest point.
-- source:
--   Jia, Strategyproof Aggregation in Euclidean Spaces: Rigidity and Median Optimality, arXiv:2609.19394 (held version, sha256 891e6125…), Theorem B.4, p.46 (PDF p.48)

import Mathlib
import Definitions.Def_EuclidSPAgg_IsStrategyproof
import Definitions.Def_EuclidSPAgg_menu
import Definitions.Def_SuperPolyak_solutionSet
open RBMSensitivity (E)

namespace EuclidSPAgg.Supplement

open EuclidSPAgg

/-- **Theorem B.4** (all-population regularity; Jia, *Strategyproof Aggregation in Euclidean Spaces: Rigidity and Median Optimality*, arXiv:2609.19394 (held version, sha256 891e6125…), p.46 (PDF p.48)). Let `f : Eⁿ → E` be
deterministic and strategyproof, with convex full range. Every unilateral menu is closed and convex,
every unilateral response is its metric projection, and `‖f(x) − f(x′)‖ ≤ ∑ᵢ ‖xᵢ − x′ᵢ‖`.

**Formalization Note** The full range is `Set.range f`; the unilateral menu is the published
`menu f i x`. "The response is the metric projection" is: the set of nearest points of the menu to
`a` (the published `SuperPolyak.nearestPoints`) is exactly `{f(a, x₋ᵢ)}`. `n ≥ 1` and `d ≥ 1` are the
paper's standing assumptions (p.8). -/
theorem theorem_B_4 (n d : ℕ) (hn : 1 ≤ n) (hd : 1 ≤ d) (f : Mech n d) (hSP : IsStrategyproof f)
    (hconv : Convex ℝ (Set.range f)) :
    (∀ (i : Fin n) (x : Fin n → E d), IsClosed (menu f i x) ∧ Convex ℝ (menu f i x) ∧
        ∀ a : E d, SuperPolyak.nearestPoints (menu f i x) a = {f (Function.update x i a)}) ∧
      ∀ x x' : Fin n → E d, ‖f x - f x'‖ ≤ ∑ i, ‖x i - x' i‖ := by sorry

end EuclidSPAgg.Supplement

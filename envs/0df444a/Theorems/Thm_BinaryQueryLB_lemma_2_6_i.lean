-- Prove2me | Theorems.Thm_BinaryQueryLB_lemma_2_6_i
-- name    : BinaryQueryLB.lemma_2_6_i
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:48:53.71948+00:00
-- url     : https://prove2.me/theorems/13a77871-e9d5-4721-8ed0-c750f8ef55c0
-- title:
--   Lemma 2.6(i) — $F_W\in F(d,R,M)$, and $F_W$ is $0.96M$-Lipschitz in $\|\cdot\|_\infty$ on $\mathbb R^d$
-- statement:
--   Let $d\ge2$, $R,M>0$, $m=\lfloor d/2\rfloor$ and $W\in\mathcal W$. Then $F_W\in F(d,R,M)$, and
--   $$
--   |F_W(y)-F_W(y')|\le 0.96\,M\,\|y-y'\|_\infty\qquad\text{for all }y,y'\in\mathbb R^d .
--   $$
--
--   So every hard function is an admissible instance of the problem class, with room to spare in the Lipschitz constant.
--
--   Differences from the source:
--   - encoding: m = ⌊d/2⌋ → m = d / 2 (natural-number division); reason: the same number
--   - encoding: ∥·∥∞ on ℝ^d → supNorm on EuclideanSpace ℝ (Fin d); reason: the maximum norm written out
-- source:
--   Shen–Zhong, Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries (manuscript, sha256 9502d824…), Lemma 2.6(i), p.13

import Mathlib
import Definitions.Def_BinaryQueryLB_FW__386b32
import Definitions.Def_BinaryQueryLB_Wset
import Definitions.Def_BinaryQueryLB_ProblemClass
import Definitions.Def_BinaryQueryLB_supNorm

namespace BinaryQueryLB

/-- **Lemma 2.6(i) (Membership).** Shen–Zhong, *Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries* (manuscript, sha256 9502d824…), Lemma 2.6(i), p.13: "Let `W ∈ 𝒲`. (i) `F_W ∈ F(d, R, M)`,
and `|F_W(y) − F_W(y′)| ≤ 0.96 M∥y − y′∥∞` for all `y, y′ ∈ R^d`."

**Formalization Note.** `d ≥ 2`, `R, M > 0` are the standing assumptions of Definitions 2.1 and
2.4; `m = d / 2`; `∥·∥∞` is `supNorm`. The Lipschitz bound holds on all of ℝ^d. -/
theorem lemma_2_6_i (d : ℕ) (hd : 2 ≤ d) (R M : ℝ) (hR : 0 < R) (hM : 0 < M)
    (W : Fin (d / 2) → EuclideanSpace ℝ (Fin (d / 2))) (hW : W ∈ Wset (d / 2)) :
    FW d R M W ∈ ProblemClass d R M ∧
      ∀ y y' : EuclideanSpace ℝ (Fin d), |FW d R M W y - FW d R M W y'| ≤ 0.96 * M * supNorm (y - y') := by sorry

end BinaryQueryLB

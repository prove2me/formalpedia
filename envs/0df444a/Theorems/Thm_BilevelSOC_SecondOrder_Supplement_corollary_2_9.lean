-- Prove2me | Theorems.Thm_BilevelSOC_SecondOrder_Supplement_corollary_2_9
-- name    : BilevelSOC.SecondOrder.Supplement.corollary_2_9
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T07:40:44.474347+00:00
-- url     : https://prove2.me/theorems/dae9e35d-c7a7-465f-b970-53d17133c4b0
-- title:
--   Corollary 2.9 — Lower-Dini exclusion criterion for first-order growth
-- statement:
--   Let $\theta:\mathbb R^n\to\overline{\mathbb R}$ and $c_i:\mathbb R^n\to\overline{\mathbb R}$ for $i=1,\ldots,k$. Set $X=\{a:c_i(a)\le0\ \forall i\}$ and $I(x)=\{i:c_i(x)=0\}$. Suppose $X$ is closed, $x\in X$ has finite objective value, every $c_i$ is locally Lipschitz at $x$, and $\theta$ has an extended-real Hadamard derivative $\theta^*(x;d)$ in every direction. If
--
--   $$\theta^*(x;d)\le0,\qquad c_i^-(x;d)\le0\quad(i\in I(x))\quad\Longrightarrow\quad d=0,$$
--
--   then there are a neighborhood $U$ and $C>0$ such that $\theta(a)\ge\theta(x)+C\|a-x\|_2$ for all $a\in X\cap U$. This is a lower-Dini exclusion criterion for first-order growth; the objective may be infinite away from the reference point.
--
--   Differences from the source:
--   - reading: θ*(x̄;d) in Corollary 2.9 with the context of Proposition 2.7 → an existing extended-real Hadamard derivative in every direction, a finite reference objective value, and closed inequality feasible set; reason: the corollary explicitly follows from Proposition 2.7 and inherits the standing constrained-problem context on pp. 6–8
--   - encoding: extended-real functions locally Lipschitz at x̄ → constraint functions remain EReal-valued, with real representatives equal on a neighborhood and Lipschitz there; reason: local Lipschitzness is a finite local property; no assumption makes the objective real everywhere or locally Lipschitz
-- source:
--   Mehlitz & Zemkoho, Sufficient Optimality Conditions in Bilevel Programming, arXiv:1911.01647v1, p. 8, Corollary 2.9

import Mathlib
import Definitions.Def_BilevelSOC_SecondOrder_Supplement_FirstOrder
open scoped Topology

namespace BilevelSOC.SecondOrder.Supplement
theorem corollary_2_9 {n k : ℕ} (θ : E n → EReal) (c : Fin k → E n → EReal)
    (x : E n) (θstar : E n → EReal)
    (hfinite : ∃ v : ℝ, θ x = (v : EReal))
    (hfeas : ∀ i, c i x ≤ 0)
    (hclosed : IsClosed {a | ∀ i, c i a ≤ 0})
    (hLip : ∀ i, ELocallyLipschitzAt (c i) x)
    (hHad : ∀ d, HasEHadamardDirDerivAt θ x d (θstar d))
    (hexclude : ∀ d, θstar d ≤ 0 →
      (∀ i, c i x = 0 → lowerDini (c i) x d ≤ 0) → d = 0) :
    EGrowthCondition θ {a | ∀ i, c i a ≤ 0} x := by sorry
end BilevelSOC.SecondOrder.Supplement

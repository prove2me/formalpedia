-- Prove2me | Theorems.Thm_EngagementOpt_Salad_eq_7
-- name    : EngagementOpt.Salad.eq_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T09:42:48.238208+00:00
-- url     : https://prove2.me/theorems/fc7ac911-7d14-43a8-9469-f3d785ac1eae
-- title:
--   (7), p. 18 — 1 ≤ a ≤ 1/(1 − α) when p ≤ α < 1
-- statement:
--   Let $\omega=(p,q,\bar v)\in\Omega$ and let $\alpha<1$ with $p\le\alpha$. Then $a=\frac{1}{1-p}$ satisfies
--   $$1\ \le\ a\ \le\ \frac{1}{1-\alpha}.$$
--
--   In the proof of Theorem 4.2 this is applied to $a_S$ and $a_T$, using condition 1 of the theorem.
--
--   **Formalization Note** The hypothesis $\alpha<1$ is implicit in the paper and is needed: for $\alpha=1$, Lean's $1/0=0$ would make the upper bound false.
-- source:
--   Kleinberg, Mullainathan, Raghavan, The Challenge of Understanding What Users Want, arXiv:2202.11776v3, p. 18, proof of Theorem 4.2, eq. (7)

import Mathlib
import Definitions.Def_EngagementOpt_Salad_Model

namespace EngagementOpt.Salad

/-- (7), p. 18: if `ω ∈ Ω`, `p ≤ α` and `α < 1`, then `1 ≤ a ≤ 1/(1 − α)`. -/
theorem eq_7 (ω : EngagementOpt.Misalign.Params) (hω : EngagementOpt.Misalign.InOmega ω) (α : ℝ) (hα : α < 1) (hp : ω.p ≤ α) :
    1 ≤ aCoef ω ∧ aCoef ω ≤ 1 / (1 - α) := by sorry

end EngagementOpt.Salad

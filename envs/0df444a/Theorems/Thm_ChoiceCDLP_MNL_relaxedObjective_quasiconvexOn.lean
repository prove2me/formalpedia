-- Prove2me | Theorems.Thm_ChoiceCDLP_MNL_relaxedObjective_quasiconvexOn
-- name    : ChoiceCDLP.MNL.relaxedObjective_quasiconvexOn
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T07:59:01.571714+00:00
-- url     : https://prove2.me/theorems/17a37918-443f-484c-80f8-444fbcdd70b3
-- title:
--   Proof of Proposition 6 — h(z) = wᵀz/(eᵀz + v_0) is quasiconvex on the box 𝒟 (h(0) := 0 when v_0 = 0)
-- statement:
--   Let $\iota$ be a finite index set, $v_j > 0$ for every $j$, $v_0 \ge 0$ and $w \in \mathbb{R}^\iota$ arbitrary. The function
--   $$h(z) = \frac{\sum_j w_j z_j}{\sum_j z_j + v_0}$$
--   is **quasiconvex** on the box $\mathcal{D} = \prod_j [0, v_j]$: for all $z, z' \in \mathcal{D}$ and $\theta \in [0,1]$,
--   $$h(\theta z + (1-\theta) z') \le \max\{h(z), h(z')\},$$
--   equivalently every sublevel set $\{ z \in \mathcal{D} : h(z) \le c\}$ is convex.
--
--   The paper obtains this from Avriel (1976, p. 156) on ratios of linear functions, and then uses that a quasiconvex function on a compact convex set attains its maximum at boundary points.
--
--   **Formalization Note.** Stated with Mathlib's `QuasiconvexOn ℝ (Set.Icc 0 v) h`. The denominator vanishes on $\mathcal{D}$ only at $z = 0$ when $v_0 = 0$; there $h(0) = 0$ by Lean's $0/0 = 0$, which is the paper's definition $h(0) := 0$, so the statement covers that case as the paper does.
-- source:
--   Liu, van Ryzin, On the Choice-Based Linear Programming Model for Network Revenue Management, Manuf. Serv. Oper. Manag. 10(2), 2008, p. 309, Appendix, proof of Proposition 6 (quasiconvexity of h via Avriel 1976, p. 156)

import Mathlib
import Definitions.Def_ChoiceCDLP_MNL_relaxedObjective

namespace ChoiceCDLP.MNL

/-- Proof of Proposition 6 (p. 309): the ratio of linear functions
`h(z) = wᵀz / (eᵀz + v₀)` is quasiconvex on the box `𝒟 = ∏_j [0, v_j]`, including the case
`v₀ = 0` with `h(0) := 0` (Lean's `0 / 0 = 0`). -/
theorem relaxedObjective_quasiconvexOn {ι : Type*} [Fintype ι] (v w : ι → ℝ) (v₀ : ℝ)
    (hv : ∀ j, 0 < v j) (hv₀ : 0 ≤ v₀) :
    QuasiconvexOn ℝ (Set.Icc 0 v) (relaxedObjective w v₀) := by sorry

end ChoiceCDLP.MNL

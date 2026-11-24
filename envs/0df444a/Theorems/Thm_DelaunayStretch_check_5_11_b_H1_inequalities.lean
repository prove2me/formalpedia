-- Prove2me | Theorems.Thm_DelaunayStretch_check_5_11_b_H1_inequalities
-- name    : DelaunayStretch.check_5_11_b_H1_inequalities
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-24T03:14:18.963656+00:00
-- url     : https://prove2.me/theorems/1d935922-5db2-41dc-ac2b-f0587de8dede
-- title:
--   Proposition 5.11(b): the inequalities (5.9) for $H_\star$ with $R=\pm\frac1{50}$
-- statement:
--   Here $V,R,B,D$ are the coefficient functions of Definition 5.2 for the explicit function $H_\star$ of Theorem 5.1 (definition `DelaunayStretch_HstarCoefficients`), $\sigma(\gamma)=\gamma-\cos^2\gamma\,V(\gamma,0,1)$, $k(\gamma)=\frac\pi2-\cos\gamma$ and $U_0=1.59485994$.
--
--   For every $\gamma\in[0,\frac\pi2)$ and each $s\in\{\frac1{50},-\frac1{50}\}$, with $m_1=\cos^2\gamma\,(B(\gamma)+s)$ and $m_2=\cos^2\gamma\,D(\gamma)$,
--
--   $$
--   |\sigma+m_1|\le k(\gamma),\qquad \big|\sigma-\tfrac12m_1+\tfrac32m_2\big|\le k(\gamma),\qquad |\sigma-2m_1-2m_2|\le k(\gamma).
--   $$
--
--   With Proposition 5.11(a) and Lemma 5.8, these inequalities give (H1) for $H_\star$. The paper checks them with interval arithmetic in the single variable $\gamma$.
-- source:
--   Mo, Cheng, Ding, The Stretch Factor of Planar Delaunay Triangulations Is Nearly Determined, arXiv:2609.07979v6, Proposition 5.11(b) (p.38); docs/VERIFICATION.md §2.4 of the archive

import Mathlib
import Definitions.Def_DelaunayStretch_HstarCoefficients

namespace DelaunayStretch

/-- **Proposition 5.11(b)** (p.38): the inequalities (5.9) for `H⋆` with `R(γ, a, b)` replaced by `1/50` and by `−1/50`, for all `γ ∈ [0, π/2)`. -/
theorem check_5_11_b_H1_inequalities :
    ∀ γ : ℝ, 0 ≤ γ → γ < Real.pi / 2 → ∀ s : ℝ, (s = 1 / 50 ∨ s = -(1 / 50)) →
      |(γ - Real.cos γ ^ 2 * familyV hstarV γ 0 1) + Real.cos γ ^ 2 * (familySpline hstarB γ + s)| ≤
          Real.pi / 2 - Real.cos γ ∧
      |(γ - Real.cos γ ^ 2 * familyV hstarV γ 0 1) - Real.cos γ ^ 2 * (familySpline hstarB γ + s) / 2 +
          3 / 2 * (Real.cos γ ^ 2 * familySpline hstarD γ)| ≤ Real.pi / 2 - Real.cos γ ∧
      |(γ - Real.cos γ ^ 2 * familyV hstarV γ 0 1) - 2 * (Real.cos γ ^ 2 * (familySpline hstarB γ + s)) -
          2 * (Real.cos γ ^ 2 * familySpline hstarD γ)| ≤ Real.pi / 2 - Real.cos γ := by sorry

end DelaunayStretch

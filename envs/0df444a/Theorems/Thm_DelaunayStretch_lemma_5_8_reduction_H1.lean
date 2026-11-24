-- Prove2me | Theorems.Thm_DelaunayStretch_lemma_5_8_reduction_H1
-- name    : DelaunayStretch.lemma_5_8_reduction_H1
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-24T03:13:54.779844+00:00
-- url     : https://prove2.me/theorems/0fe54a5b-d8df-4e75-b893-e778ddb7b84f
-- title:
--   Lemma 5.8: reduction of (H1) to inequalities in $\gamma$
-- statement:
--   Here $H\in\mathcal H$ is the member of the family of Definition 5.2 with coefficients $V_{ijl},R_{ijl},B_l,D_l$; $V,R,B,D$ are the coefficient functions of Definition 5.2, $\sigma(\gamma)=\gamma-\cos^2\gamma\,V(\gamma,0,1)$ and $k(\gamma)=\frac\pi2-\cos\gamma$.
--
--   Suppose that $\bar R\ge0$ satisfies $|R(\gamma,a,b)|\le\bar R$ on $[0,\frac\pi2]\times[0,1]^2$. Suppose also that for every $\gamma\in[0,\frac\pi2)$ and each $s\in\{\bar R,-\bar R\}$, with $m_1=\cos^2\gamma\,(B(\gamma)+s)$ and $m_2=\cos^2\gamma\,D(\gamma)$,
--
--   $$
--   |\sigma+m_1|\le k(\gamma),\qquad \big|\sigma-\tfrac12m_1+\tfrac32m_2\big|\le k(\gamma),\qquad |\sigma-2m_1-2m_2|\le k(\gamma).
--   $$
--
--   Then $H$ satisfies (H1): $|H(\gamma,\varphi,\theta,\psi_1)-H(\gamma,\varphi,\theta,\psi_2)|\le|\psi_1-\psi_2|$ for all $(\gamma,\varphi,\theta)\in\Omega$ and all $\psi_1,\psi_2\in\mathbb R$.
--
--   The three numbers are the Bernstein coefficients of $k\,\partial_\psi H^c$ as a quadratic in $\xi^2$. The lemma turns the Lipschitz condition (H1), which quantifies over all real $\psi$, into one-variable inequalities.
-- source:
--   Mo, Cheng, Ding, The Stretch Factor of Planar Delaunay Triangulations Is Nearly Determined, arXiv:2609.07979v6, Lemma 5.8 (p.36), last claim

import Mathlib
import Definitions.Def_DelaunayStretch_FamilyPieces
import Definitions.Def_DelaunayStretch_SatisfiesH0toH4

namespace DelaunayStretch

/-- **Lemma 5.8 (Reduction of (H1))** (p.36), in its final form: if `|R| ≤ R̄` on `[0, π/2] × [0, 1]²` and the inequalities (5.9) hold with `R(γ, a, b)` replaced by `R̄` and by `−R̄` for all `γ ∈ [0, π/2)`, then `H` satisfies (H1). -/
theorem lemma_5_8_reduction_H1 (V : Fin 12 → Fin 12 → Fin 35 → ℚ) (R : Fin 6 → Fin 6 → Fin 35 → ℚ)
    (Bc Dc : Fin 35 → ℚ) (Rb : ℝ) (hRb : 0 ≤ Rb)
    (hR : ∀ γ a b : ℝ, 0 ≤ γ → γ ≤ Real.pi / 2 → 0 ≤ a → a ≤ 1 → 0 ≤ b → b ≤ 1 →
      |familyR R γ a b| ≤ Rb)
    (h59 : ∀ γ : ℝ, 0 ≤ γ → γ < Real.pi / 2 → ∀ s : ℝ, (s = Rb ∨ s = -Rb) →
      |(γ - Real.cos γ ^ 2 * familyV V γ 0 1) + Real.cos γ ^ 2 * (familySpline Bc γ + s)| ≤
          Real.pi / 2 - Real.cos γ ∧
      |(γ - Real.cos γ ^ 2 * familyV V γ 0 1) - Real.cos γ ^ 2 * (familySpline Bc γ + s) / 2 +
          3 / 2 * (Real.cos γ ^ 2 * familySpline Dc γ)| ≤ Real.pi / 2 - Real.cos γ ∧
      |(γ - Real.cos γ ^ 2 * familyV V γ 0 1) - 2 * (Real.cos γ ^ 2 * (familySpline Bc γ + s)) -
          2 * (Real.cos γ ^ 2 * familySpline Dc γ)| ≤ Real.pi / 2 - Real.cos γ) :
    CondH1 (familyH V R Bc Dc) := by sorry

end DelaunayStretch

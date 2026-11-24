-- Prove2me | Theorems.Thm_DelaunayStretch_proposition_5_11_H1_H3
-- name    : DelaunayStretch.proposition_5_11_H1_H3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-24T03:06:41.819063+00:00
-- url     : https://prove2.me/theorems/5c17ce90-154c-46fe-9788-a09c6b67af27
-- title:
--   Proposition 5.11: $H_\star$ satisfies (H1), (H3) and (H2) on the pieces at level $U_0$
-- statement:
--   Let $H_\star$ be the explicit function of Theorem 5.1 and $U_0=1.59485994$. Then:
--
--   1. (H1) For all $(\gamma,\varphi,\theta)\in\Omega$ and all $\psi_1,\psi_2\in\mathbb R$,
--   $$
--   |H_\star(\gamma,\varphi,\theta,\psi_1)-H_\star(\gamma,\varphi,\theta,\psi_2)|\le|\psi_1-\psi_2| .
--   $$
--   2. (H3) For all $(\gamma,\varphi,\theta)\in\Omega$,
--   $$
--   H_\star(\gamma,\varphi,\theta,\gamma)\ge\tfrac\pi2-U_0\cos\gamma,\qquad H_\star(\gamma,\varphi,\theta,-\gamma)\le-\tfrac\pi2+U_0\cos\gamma .
--   $$
--   3. (H2 on the pieces) For every $z\in\Omega\times\mathbb R$ with $\gamma\ge0$ and every gradient $\nabla$ of the pieces of Definition 5.5 at $z$, we have $\nabla_\theta\ge|\nabla_\varphi|$.
--
--   With Lemma 5.6, this gives (H0)–(H3) for $H_\star$, as stated in Proposition 5.11. The paper proves it by the reductions of Lemmas 5.8–5.10 and computer-assisted checks in at most three variables.
-- source:
--   Mo, Cheng, Ding, The Stretch Factor of Planar Delaunay Triangulations Is Nearly Determined, arXiv:2609.07979v6, Proposition 5.11 (p.38), with Lemmas 5.7–5.10 (pp.36–37)

import Mathlib
import Definitions.Def_DelaunayStretch_HstarCoefficients
import Definitions.Def_DelaunayStretch_SatisfiesH0toH4

namespace DelaunayStretch

/-- **Proposition 5.11 ((H0)–(H3) for `H⋆`)** (p.38), in the form used by Lemma 5.7: `H⋆`
satisfies (H1) and (H3) at level `U₀ = 1.59485994`, and `∇θ ≥ |∇φ|` for every gradient `∇` of
the pieces at points with `γ ≥ 0` (the hypothesis of Lemma 5.7(2)). -/
theorem proposition_5_11_H1_H3 :
    CondH1 Hstar ∧ CondH3 (159485994 / 100000000 : ℝ) Hstar ∧
      ∀ z g : R4, IsPieceGradient hstarV hstarR hstarB hstarD z g → |g.2.1| ≤ g.2.2.1 := by sorry

end DelaunayStretch

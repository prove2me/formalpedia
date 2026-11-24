-- Prove2me | Theorems.Thm_DelaunayStretch_lemma_5_10_reduction_H3
-- name    : DelaunayStretch.lemma_5_10_reduction_H3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-24T03:13:51.740407+00:00
-- url     : https://prove2.me/theorems/1c112b14-f246-4533-8890-34f8d39c8228
-- title:
--   Lemma 5.10: reduction of (H3) to the corner $(a,b)=(0,0)$
-- statement:
--   Here $H\in\mathcal H$ is the member of the family of Definition 5.2 with coefficients $V_{ijl},R_{ijl},B_l,D_l$; $V,R,B,D$ are the coefficient functions of Definition 5.2, $\sigma(\gamma)=\gamma-\cos^2\gamma\,V(\gamma,0,1)$ and $k(\gamma)=\frac\pi2-\cos\gamma$.
--
--   Let the coefficients satisfy (5.3)–(5.4), and suppose that $\nabla_\theta\ge|\nabla_\varphi|$ for every gradient $\nabla$ of the pieces at points with $\gamma\ge0$ (condition (H2) on the pieces). Suppose that for every $\gamma\in[0,\frac\pi2)$, at $\xi=\gamma/k(\gamma)$,
--
--   $$
--   \cos^2\gamma\,V(\gamma,0,0)+\sigma(\gamma)\,\xi+\cos^2\gamma\big[B(\gamma)(\xi-\xi^3)+D(\gamma)(\xi^3-\xi^5)\big]\ge\tfrac\pi2-U\cos\gamma .\qquad(5.11)
--   $$
--
--   Then $H$ satisfies (H3) at level $U$: $H(\gamma,\varphi,\theta,\gamma)\ge\frac\pi2-U\cos\gamma$ and $H(\gamma,\varphi,\theta,-\gamma)\le-\frac\pi2+U\cos\gamma$ for all $(\gamma,\varphi,\theta)\in\Omega$.
--
--   By (H2), the worst case of the first inequality of (H3) is the corner $(a,b)=(0,0)$, where $R=0$. The second inequality and the case $\gamma<0$ follow from the reflections of Lemma 5.4.
-- source:
--   Mo, Cheng, Ding, The Stretch Factor of Planar Delaunay Triangulations Is Nearly Determined, arXiv:2609.07979v6, Lemma 5.10 (p.37), with Lemma 5.7(3) (p.36)

import Mathlib
import Definitions.Def_DelaunayStretch_FamilyPieces
import Definitions.Def_DelaunayStretch_SatisfiesH0toH4

namespace DelaunayStretch

/-- **Lemma 5.10 (Reduction of (H3))** (p.37), with Lemma 5.7(3): let `H ∈ 𝓗` satisfy (H2) on the pieces with `γ ≥ 0`; if (5.11) holds for every `γ ∈ [0, π/2)` at `ξ = γ/k(γ)`, then `H` satisfies (H3) at level `U`. -/
theorem lemma_5_10_reduction_H3 (V : Fin 12 → Fin 12 → Fin 35 → ℚ) (R : Fin 6 → Fin 6 → Fin 35 → ℚ)
    (Bc Dc : Fin 35 → ℚ) (hc : FamilyCoeffConditions V R Bc Dc) (U : ℝ)
    (h2 : ∀ z g : R4, IsPieceGradient V R Bc Dc z g → |g.2.1| ≤ g.2.2.1)
    (h511 : ∀ γ : ℝ, 0 ≤ γ → γ < Real.pi / 2 →
      Real.pi / 2 - U * Real.cos γ ≤
        Real.cos γ ^ 2 * familyV V γ 0 0 +
          (γ - Real.cos γ ^ 2 * familyV V γ 0 1) * (γ / (Real.pi / 2 - Real.cos γ)) +
          Real.cos γ ^ 2 * (familySpline Bc γ * ((γ / (Real.pi / 2 - Real.cos γ)) -
              (γ / (Real.pi / 2 - Real.cos γ)) ^ 3) +
            familySpline Dc γ * ((γ / (Real.pi / 2 - Real.cos γ)) ^ 3 -
              (γ / (Real.pi / 2 - Real.cos γ)) ^ 5))) :
    CondH3 U (familyH V R Bc Dc) := by sorry

end DelaunayStretch

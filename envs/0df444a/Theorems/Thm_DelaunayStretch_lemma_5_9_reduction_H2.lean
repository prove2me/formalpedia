-- Prove2me | Theorems.Thm_DelaunayStretch_lemma_5_9_reduction_H2
-- name    : DelaunayStretch.lemma_5_9_reduction_H2
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-24T03:14:23.46056+00:00
-- url     : https://prove2.me/theorems/b1fae893-f893-4bc2-a300-e1b71604b691
-- title:
--   Lemma 5.9: reduction of (H2) to monotonicity of $V\pm\frac25R$
-- statement:
--   Here $H\in\mathcal H$ is the member of the family of Definition 5.2 with coefficients $V_{ijl},R_{ijl},B_l,D_l$; $V,R,B,D$ are the coefficient functions of Definition 5.2, $\sigma(\gamma)=\gamma-\cos^2\gamma\,V(\gamma,0,1)$ and $k(\gamma)=\frac\pi2-\cos\gamma$.
--
--   Suppose that on $[0,\frac\pi2]\times[0,1]^2$, for both signs,
--
--   $$
--   \partial_a\big(V\pm\tfrac25R\big)\ge0,\qquad \partial_b\big(V\pm\tfrac25R\big)\ge0 .
--   $$
--
--   Then for every $z\in\Omega\times\mathbb R$ with $\gamma\ge0$ and every gradient $\nabla$ of the pieces of Definition 5.5 at $z$, we have $\nabla_\theta\ge|\nabla_\varphi|$. By Lemma 5.7(2) this gives condition (H2).
--
--   The constant $\frac25$ bounds $|\xi-\xi^3|$ for $|\xi|\le1$. The lemma turns the monotonicity condition (H2) into sign conditions on derivatives of the coefficient functions in the positions $a,b$.
-- source:
--   Mo, Cheng, Ding, The Stretch Factor of Planar Delaunay Triangulations Is Nearly Determined, arXiv:2609.07979v6, Lemma 5.9 (p.37), with Lemma 5.7(2) (p.36)

import Mathlib
import Definitions.Def_DelaunayStretch_FamilyPieces
import Definitions.Def_DelaunayStretch_SatisfiesH0toH4

namespace DelaunayStretch

/-- **Lemma 5.9 (Reduction of (H2))** (p.37): if `∂_a(V ± (2/5)R) ≥ 0` and `∂_b(V ± (2/5)R) ≥ 0` on `[0, π/2] × [0, 1]²` for both signs, then `∇θ ≥ |∇φ|` for every gradient of the pieces at points with `γ ≥ 0` (which gives (H2) by Lemma 5.7(2)). -/
theorem lemma_5_9_reduction_H2 (V : Fin 12 → Fin 12 → Fin 35 → ℚ) (R : Fin 6 → Fin 6 → Fin 35 → ℚ)
    (Bc Dc : Fin 35 → ℚ)
    (hmono : ∀ γ a b : ℝ, 0 ≤ γ → γ ≤ Real.pi / 2 → 0 ≤ a → a ≤ 1 → 0 ≤ b → b ≤ 1 →
      ∀ s : ℝ, (s = 2 / 5 ∨ s = -(2 / 5)) →
        0 ≤ deriv (fun a' => familyV V γ a' b + s * familyR R γ a' b) a ∧
        0 ≤ deriv (fun b' => familyV V γ a b' + s * familyR R γ a b') b) :
    ∀ z g : R4, IsPieceGradient V R Bc Dc z g → |g.2.1| ≤ g.2.2.1 := by sorry

end DelaunayStretch

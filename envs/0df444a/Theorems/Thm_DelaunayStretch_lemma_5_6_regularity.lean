-- Prove2me | Theorems.Thm_DelaunayStretch_lemma_5_6_regularity
-- name    : DelaunayStretch.lemma_5_6_regularity
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-24T03:06:19.047991+00:00
-- url     : https://prove2.me/theorems/c55d9fc0-c292-400b-80d4-4486662fcf0d
-- title:
--   Lemma 5.6: pieces of $H\in\mathcal H$ form a piecewise $C^1$ structure; (H0); reflection of gradients
-- statement:
--   Let $H\in\mathcal H$ be a member of the family of Definition 5.2, with coefficients satisfying (5.3) and (5.4). Then:
--
--   1. The six sets and functions of Definition 5.5 form a piecewise $C^1$ structure for $H$ in the sense of Definition 4.5. These are the central piece $\{\gamma\ge0,\ |\xi|\le1\}$ with $H^c$, the outer pieces $\{\gamma\ge0,\ \pm\xi\ge1\}$ with $H^\pm$, and their images under $\rho_1(\gamma,\varphi,\theta,\psi)=(-\gamma,-\varphi,\theta,-\psi)$ with the composed functions.
--   2. $H$ is continuous and locally Lipschitz on $\Omega\times\mathbb R$, i.e. $H$ satisfies (H0).
--   3. (Lemma 5.6(2)) Let $\nabla$ be an incident gradient of $H$ at $z\in\Omega\times\mathbb R$ with respect to this structure. Then either $\nabla$ is a gradient of the pieces at $z$ (a piece with $\gamma\ge0$ containing $z$), or $\nabla'=(-\nabla_\gamma,-\nabla_\varphi,\nabla_\theta,-\nabla_\psi)$ is a gradient of the pieces at $\rho_1(z)$ and
--   $$
--   \mathcal E_U[H;\nabla'](\rho_1(z))=\mathcal E_U[H;\nabla](z)\qquad\text{for every }U\in\mathbb R .
--   $$
--
--   This lemma reduces conditions (H2) and (H4) for members of $\mathcal H$ to the gradients of the three pieces at points with $\gamma\ge0$ (Lemma 5.7).
--
--   **Formalization Note** The structure is asserted to exist, together with the property of its incident gradients that Lemma 5.7 uses; gradients of the pieces are `IsPieceGradient` of `Def_DelaunayStretch_FamilyPieces`.
-- source:
--   Mo, Cheng, Ding, The Stretch Factor of Planar Delaunay Triangulations Is Nearly Determined, arXiv:2609.07979v6, Lemma 5.6 (1)–(2), pp.34–35, with Definition 5.5 (p.34)

import Mathlib
import Definitions.Def_DelaunayStretch_FamilyPieces
import Definitions.Def_DelaunayStretch_SatisfiesH0toH4

namespace DelaunayStretch

/-- **Lemma 5.6 (Regularity)** (pp.34–35), with part (2). For every member `H` of the family
`𝓗`, the six sets and functions of Definition 5.5 form a piecewise `C¹` structure for `H`, and
`H` is continuous and locally Lipschitz (H0). Every incident gradient at `z` is a gradient of
the pieces at `z` (pieces with `γ ≥ 0`), or `z` lies in the image under `ρ₁` of a piece and the
reflected vector `(−∇γ, −∇φ, ∇θ, −∇ψ)` is a gradient of that piece at `ρ₁(z)`, with
`𝓔_U[H; ∇′](ρ₁(z)) = 𝓔_U[H; ∇](z)` for every `U`. -/
theorem lemma_5_6_regularity (V : Fin 12 → Fin 12 → Fin 35 → ℚ) (R : Fin 6 → Fin 6 → Fin 35 → ℚ)
    (Bc Dc : Fin 35 → ℚ) (hc : FamilyCoeffConditions V R Bc Dc) :
    ∃ P : PiecewiseC1 (familyH V R Bc Dc), CondH0 (familyH V R Bc Dc) ∧
      ∀ z ∈ OmegaTimesR, ∀ g : R4, P.IncidentGradient z g →
        IsPieceGradient V R Bc Dc z g ∨
        (IsPieceGradient V R Bc Dc (reflect1 z) (-g.1, -g.2.1, g.2.2.1, -g.2.2.2) ∧
          ∀ U : ℝ, pencilResidual U (familyH V R Bc Dc) (-g.1, -g.2.1, g.2.2.1, -g.2.2.2)
              (reflect1 z) = pencilResidual U (familyH V R Bc Dc) g z) := by sorry

end DelaunayStretch

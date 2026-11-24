-- Prove2me | Theorems.Thm_DelaunayStretch_proposition_6_7_H4
-- name    : DelaunayStretch.proposition_6_7_H4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-24T03:07:01.705357+00:00
-- url     : https://prove2.me/theorems/5df11d63-2e26-4fd4-90b2-f27f1ce00c42
-- title:
--   Proposition 6.7: (H4) for $H_\star$ at level $U_0$ on the pieces
-- statement:
--   Let $H_\star$ be the explicit function of Theorem 5.1 and $U_0=1.59485994$. For every $z=(\gamma,\varphi,\theta,\psi)\in\Sigma$ and every gradient $\nabla$ of the pieces of Definition 5.5 at $z$ (pieces with $\gamma\ge0$), the pencil residual of Definition 4.3 satisfies
--
--   $$
--   \mathcal E_{U_0}[H_\star;\nabla](z)=\cos\theta\big(\tfrac\pi2-\theta\big)+\sin\theta-U_0\cos\varphi-\cos\theta\,H_\star(z)+\cos\theta(\psi-\varphi)\nabla_\psi-\mathcal A\,\nabla_\gamma+\sin\theta\,\nabla_\theta\le0,
--   $$
--
--   where $\mathcal A=(\sin\varphi-\sin\gamma\cos\theta)/\cos\gamma$. Since $\gamma\ge0$ is required in the definition of the gradients of the pieces, these points have $\gamma\ge0$.
--
--   By Lemma 5.7(4) this gives condition (H4) for $H_\star$. The condition has no slack near the corner curve. The paper verifies it with the corner lemmas of §6.3 and a cover of about $1.04$ million boxes checked in interval arithmetic.
-- source:
--   Mo, Cheng, Ding, The Stretch Factor of Planar Delaunay Triangulations Is Nearly Determined, arXiv:2609.07979v6, Proposition 6.7 (p.43), with Lemma 5.7(4) (p.36) and Lemma 6.1 (p.39)

import Mathlib
import Definitions.Def_DelaunayStretch_HstarCoefficients
import Definitions.Def_DelaunayStretch_SatisfiesH0toH4

namespace DelaunayStretch

/-- **Proposition 6.7 ((H4) for `H⋆`)** (p.43), in the form of Lemma 5.7(4): the pencil
residual `𝓔_{U₀}[H⋆; ∇](z)` is `≤ 0` for every `z ∈ Σ` and every gradient `∇` of the pieces at
`z` (pieces with `γ ≥ 0`). -/
theorem proposition_6_7_H4 :
    ∀ z ∈ SigmaSet, ∀ g : R4, IsPieceGradient hstarV hstarR hstarB hstarD z g →
      pencilResidual (159485994 / 100000000 : ℝ) Hstar g z ≤ 0 := by sorry

end DelaunayStretch

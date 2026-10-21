-- Prove2me | Theorems.Thm_CauchyRiemannIndex_asymptoticCZIndex_diamond
-- name    : CauchyRiemannIndex.asymptoticCZIndex_diamond
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-20T15:46:43.836485+00:00
-- url     : https://prove2.me/theorems/bbf40b9f-dfb3-4254-acd0-8c08708ffa95
-- title:
--   The Conley–Zehnder index of a block-diagonal asymptotic operator is the sum of the block indices
-- statement:
--   Let $A:\mathbb{R}\to\mathbb{R}^{2m_1\times2m_1}$ and $B:\mathbb{R}\to\mathbb{R}^{2m_2\times2m_2}$ be continuous $1$-periodic loops of symmetric matrices whose asymptotic operators $-J_0\partial_t-A$ and $-J_0\partial_t-B$ are nondegenerate. Let $A\diamond B$ be the block-diagonal loop on $\mathbb{R}^{2(m_1+m_2)}=\mathbb{R}^{2m_1}\oplus\mathbb{R}^{2m_2}$, where $(q',p')\oplus(q'',p'')\mapsto(q',q'',p',p'')$. Then $A\diamond B$ is a continuous $1$-periodic loop of symmetric matrices, $-J_0\partial_t-A\diamond B$ is nondegenerate, and
--   $$\mu_{CZ}(-J_0\partial_t-A\diamond B)=\mu_{CZ}(-J_0\partial_t-A)+\mu_{CZ}(-J_0\partial_t-B).$$
--
--   This is the direct-sum property of the Conley–Zehnder index of asymptotic operators. It is used to compute indices of block-diagonal asymptotic operators.
--
--   **Formalization Note** The block-diagonal sum is `ConleyZehnder.diamond`, applied pointwise. Loops are `IsSymLoop`, nondegeneracy is `IsNondegenerate` (no eigenvalue $1$ of $\Psi(1)$, where $\Psi'=J_0S\Psi$, $\Psi(0)=\mathrm{Id}$) and the index is `asymptoticCZIndex`, all from the setting module.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 3 (direct-sum property of μ_CZ); Gutt, arXiv:1307.7239, Proposition 8 (4)

import Definitions.Def_CauchyRiemannIndex_Setting
import Definitions.Def_ConleyZehnder_Setting

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

/-- For loops `A`, `B` of symmetric matrices with nondegenerate asymptotic operators, the
block-diagonal loop `A ⋄ B` is a loop of symmetric matrices, its asymptotic operator is
nondegenerate, and `μ_CZ(-J₀ ∂ₜ - A ⋄ B) = μ_CZ(-J₀ ∂ₜ - A) + μ_CZ(-J₀ ∂ₜ - B)`. -/
theorem asymptoticCZIndex_diamond {m₁ m₂ : ℕ} (A : ℝ → Mat m₁) (B : ℝ → Mat m₂)
    (hA : IsSymLoop A) (hB : IsSymLoop B) (hnA : IsNondegenerate A) (hnB : IsNondegenerate B) :
    IsSymLoop (fun t => ConleyZehnder.diamond (A t) (B t)) ∧
      IsNondegenerate (fun t => ConleyZehnder.diamond (A t) (B t)) ∧
      asymptoticCZIndex (fun t => ConleyZehnder.diamond (A t) (B t)) =
        asymptoticCZIndex A + asymptoticCZIndex B := by
  sorry

end CauchyRiemannIndex

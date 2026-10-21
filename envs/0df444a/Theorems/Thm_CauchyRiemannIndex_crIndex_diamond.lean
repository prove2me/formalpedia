-- Prove2me | Theorems.Thm_CauchyRiemannIndex_crIndex_diamond
-- name    : CauchyRiemannIndex.crIndex_diamond
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-20T15:35:39.097417+00:00
-- url     : https://prove2.me/theorems/efa1e3e8-803b-45d1-a9fb-c20cd697df2f
-- title:
--   The Fredholm index of a Cauchy–Riemann operator on the cylinder with block-diagonal coefficient is the sum of the block indices
-- statement:
--   Let $1\le p\le\infty$ and $m_1,m_2\ge0$. Let $S_1:\mathbb{R}\times S^1\to\mathbb{R}^{2m_1\times2m_1}$ and $S_2:\mathbb{R}\times S^1\to\mathbb{R}^{2m_2\times2m_2}$ be coefficients such that the Cauchy–Riemann operators
--   $$D_{S_i}=\partial_s+J_0\partial_t+S_i:W^{1,p}(\mathbb{R}\times S^1,\mathbb{R}^{2m_i})\to L^p(\mathbb{R}\times S^1,\mathbb{R}^{2m_i})$$
--   are Fredholm. Let $S_1\diamond S_2$ be the block-diagonal coefficient on $\mathbb{R}^{2(m_1+m_2)}=\mathbb{R}^{2m_1}\oplus\mathbb{R}^{2m_2}$, where $(q',p')\oplus(q'',p'')\mapsto(q',q'',p',p'')$. Then
--   $$\operatorname{ind}D_{S_1\diamond S_2}=\operatorname{ind}D_{S_1}+\operatorname{ind}D_{S_2}.$$
--
--   This is the direct-sum property of the index on the cylinder. It lets one compute indices in dimension $2n$ from operators that split into lower-dimensional blocks.
--
--   **Formalization Note** The block-diagonal sum is `ConleyZehnder.diamond` (the embedding used for the product property of the Conley–Zehnder index), applied pointwise: `fun x => ConleyZehnder.diamond (S₁ x) (S₂ x)`. The index is `crIndex p S` $=\dim\ker D_S-\dim\operatorname{coker}D_S$ and Fredholmness is `IsFredholmCR p S` (finite-dimensional kernel, closed range of finite codimension), both from the setting module. No regularity of $S_1,S_2$ is assumed beyond Fredholmness.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 5, proof of Theorem 5.4 (direct sums), cylinder with trivial bundle

import Definitions.Def_CauchyRiemannIndex_Setting
import Definitions.Def_ConleyZehnder_Setting

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

/-- The Fredholm index of the Cauchy–Riemann operator `∂ₛ + J₀ ∂ₜ + S₁ ⋄ S₂` with block-diagonal
coefficient `S₁ ⋄ S₂` (the splitting `ℝ^{2(m₁+m₂)} = ℝ^{2m₁} ⊕ ℝ^{2m₂}` of `ConleyZehnder.diamond`) is the
sum of the indices of `∂ₛ + J₀ ∂ₜ + S₁` and `∂ₛ + J₀ ∂ₜ + S₂`, when both are Fredholm on
`W^{1,p} → L^p`. -/
theorem crIndex_diamond {m₁ m₂ : ℕ} (p : ℝ≥0∞) [Fact (1 ≤ p)] (S₁ : ℝ × ℝ → Mat m₁)
    (S₂ : ℝ × ℝ → Mat m₂) (h₁ : IsFredholmCR p S₁) (h₂ : IsFredholmCR p S₂) :
    crIndex p (fun x => ConleyZehnder.diamond (S₁ x) (S₂ x)) = crIndex p S₁ + crIndex p S₂ := by
  sorry

end CauchyRiemannIndex

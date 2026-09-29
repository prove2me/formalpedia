-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_prod_norm_norm_pow_mult_le_mul_of_mem_of_isCompact
-- name    : AutomorphicForm.exists_forall_prod_norm_norm_pow_mult_le_mul_of_mem_of_isCompact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/3194dd39-586d-5bd2-b005-bffd7c956105
-- title:
--   Uniform comparability of archimedean norms on a compact twisted window
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a finite extension of $K$, let $\sigma$ be a $K$-algebra automorphism of $L$, and write $E = L \otimes_K \mathbb{A}_{K,\infty}$ for the tensor product of $L$ with the infinite adele ring of $K$. Let $\Omega \subseteq E^\times \times E^\times$ be a compact set. Then there exists a real constant $C \ge 0$ such that for all units $\alpha, \beta, a_1, a_2 \in E^\times$ satisfying
--   $$\bigl(\alpha \cdot \tilde\sigma(a_1) \cdot a_1^{-1},\; \beta \cdot \tilde\sigma(a_2) \cdot a_2^{-1}\bigr) \in \Omega,$$
--   where $\tilde\sigma$ denotes the map induced on units by the ring endomorphism $\sigma \otimes \mathrm{id}$ of $E$ (the project's [`AutomorphicForm.sigmaTensor`](def/AutomorphicForm_TwistedOrbital.html#L199), i.e. $\sigma$ on the factor $L$ and the identity on $\mathbb{A}_{K,\infty}$), both inequalities
--   $$\prod_{v \mid \infty} \bigl\lVert \bigl(N_{E/\mathbb{A}_{K,\infty}}(\alpha)\bigr)_v \bigr\rVert^{m_v} \le C \prod_{v \mid \infty} \bigl\lVert \bigl(N_{E/\mathbb{A}_{K,\infty}}(\beta)\bigr)_v \bigr\rVert^{m_v}$$
--   and the same with $\alpha$ and $\beta$ interchanged hold; here the product is over the infinite places $v$ of $K$, $m_v$ is the multiplicity $v$.`mult`, and $N_{E/\mathbb{A}_{K,\infty}}$ is the algebra norm of $E$ over $\mathbb{A}_{K,\infty}$, whose value is evaluated at $v$ and measured in the corresponding completion.
--
--   This is the uniform two-sided comparability of the archimedean sizes of $N\alpha$ and $N\beta$ once the $\sigma$-twisted pair $(\alpha\,\tilde\sigma(a_1)a_1^{-1}, \beta\,\tilde\sigma(a_2)a_2^{-1})$ is confined to a fixed compact window, the point being that the twisting factors $\tilde\sigma(a)a^{-1}$ have norm $1$. It serves as the archimedean bookkeeping step in the estimate for twisted orbital integrals on archimedean scalar multiples, [`AutomorphicForm.exists_forall_prod_infinitePlace_norm_sub_norm_mul_le_of_isTwistedOrbitalIntegralOn_tensorArch_scalar_mul`](thm.html#AutomorphicForm.exists_forall_prod_infinitePlace_norm_sub_norm_mul_le_of_isTwistedOrbitalIntegralOn_tensorArch_scalar_mul), and its proof invokes the Iwasawa-type decomposition and compactness statement [`NumberField.InfiniteAdeleRing.exists_mem_borelSubgroup_mul_eq_and_isCompact_iInf_rowIsometrySubgroup`](thm.html#NumberField.InfiniteAdeleRing.exists_mem_borelSubgroup_mul_eq_and_isCompact_iInf_rowIsometrySubgroup).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_prod_norm_norm_pow_mult_le_mul_of_mem_of_isCompact.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_ConstantTerm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions ENNReal Pointwise
open LanglandsTunnell.CubicInduction (diagUnits2)

theorem AutomorphicForm.exists_forall_prod_norm_norm_pow_mult_le_mul_of_mem_of_isCompact
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (σ : L ≃ₐ[K] L)
    (Ω : Set ((L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ)) (hΩ : IsCompact Ω) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (α β a₁ a₂ : (L ⊗[K] InfiniteAdeleRing K)ˣ),
      (α * Units.map (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ).toMonoidHom a₁ * a₁⁻¹, β * Units.map (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ).toMonoidHom a₂ * a₂⁻¹) ∈ Ω →
      (∏ v : InfinitePlace K, ‖(Algebra.norm (InfiniteAdeleRing K) (α : (L ⊗[K] InfiniteAdeleRing K))) v‖ ^ v.mult) ≤
          C * ∏ v : InfinitePlace K, ‖(Algebra.norm (InfiniteAdeleRing K) (β : (L ⊗[K] InfiniteAdeleRing K))) v‖ ^ v.mult ∧
      (∏ v : InfinitePlace K, ‖(Algebra.norm (InfiniteAdeleRing K) (β : (L ⊗[K] InfiniteAdeleRing K))) v‖ ^ v.mult) ≤
          C * ∏ v : InfinitePlace K, ‖(Algebra.norm (InfiniteAdeleRing K) (α : (L ⊗[K] InfiniteAdeleRing K))) v‖ ^ v.mult := by sorry

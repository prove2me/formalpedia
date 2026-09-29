-- Prove2me | Theorems.Thm_AutomorphicForm_prod_norm_archIdent_pow_mult_eq_abs_algebraNorm_real
-- name    : AutomorphicForm.prod_norm_archIdent_pow_mult_eq_abs_algebraNorm_real
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/92240aef-3de5-5d3e-88a5-a58727f9675c
-- title:
--   Archimedean module equals absolute real algebra norm
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra, and let $z \in L \otimes_K \mathbb{A}_{K,\infty}$, where $\mathbb{A}_{K,\infty}$ denotes `InfiniteAdeleRing K`. Two $\mathbb{R}$-algebra structures are installed for the statement: on $\mathbb{A}_{K,\infty}$, the one transported from the mixed space $\mathbb{R}^{r_1} \times \mathbb{C}^{r_2}$ along the inverse of `InfiniteAdeleRing.ringEquiv_mixedSpace`, and on $L \otimes_K \mathbb{A}_{K,\infty}$, the one obtained from it by composing with the right inclusion $\mathbb{A}_{K,\infty} \to L \otimes_K \mathbb{A}_{K,\infty}$. The assertion is that $$\prod_{w} \lVert (\mathrm{archIdent}\, z)_w \rVert^{m_w} = \lvert N_{(L \otimes_K \mathbb{A}_{K,\infty})/\mathbb{R}}(z) \rvert,$$ the product being over all infinite places $w$ of $L$ with $m_w = w.\mathrm{mult}$ its multiplicity ($1$ for real, $2$ for complex places), where [`AutomorphicForm.archIdent K L`](def/AutomorphicForm_TwistedOrbital.html#L420) is the ring isomorphism $L \otimes_K \mathbb{A}_{K,\infty} \to \mathbb{A}_{L,\infty}$ given by the commutation isomorphism $L \otimes_K \mathbb{A}_{K,\infty} \cong \mathbb{A}_{K,\infty} \otimes_K L$ followed by the base change isomorphism attached to the infinite-place data [`M4aHerbrand.ArchSemilocal.genuineInfinitePlaceData`](def/M4aHerbrand_ArchSemilocal.html#L251) (distribute the tensor product over the places $v \mid \infty$ of $K$, apply on each factor the isomorphism $K_v \otimes_K L \cong \prod_{w \mid v} L_w$, and collapse the double product into the product over all $w \mid \infty$), and the right-hand side is the absolute value of the determinant of multiplication by $z$ as an $\mathbb{R}$-linear endomorphism.
--
--   This is the archimedean module formula: the normalised archimedean absolute value $\prod_{w \mid \infty} \lVert \cdot \rVert_w^{m_w}$ on $L \otimes_K \mathbb{A}_{K,\infty}$, which computes the scaling factor of Haar measure, coincides with the absolute norm over $\mathbb{R}$. It supplies the dictionary between the idelic norm of a determinant and the real algebra norm used in normalising archimedean integrals, and is cited in the computation of the idele norm of the determinant under the base-change isomorphism.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_prod_norm_archIdent_pow_mult_eq_abs_algebraNorm_real.lean

import Definitions.Def_AutomorphicForm_BaseChangePlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.prod_norm_archIdent_pow_mult_eq_abs_algebraNorm_real
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (z : L ⊗[K] InfiniteAdeleRing K) :
    letI : Algebra ℝ (InfiniteAdeleRing K) :=
      ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.comp
        (algebraMap ℝ (mixedEmbedding.mixedSpace K))).toAlgebra
    letI : Algebra ℝ (L ⊗[K] InfiniteAdeleRing K) :=
      ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K).toRingHom.comp
        (algebraMap ℝ (InfiniteAdeleRing K))).toAlgebra
    ∏ w : InfinitePlace L, ‖AutomorphicForm.archIdent K L z w‖ ^ w.mult = |Algebra.norm ℝ z| := by sorry

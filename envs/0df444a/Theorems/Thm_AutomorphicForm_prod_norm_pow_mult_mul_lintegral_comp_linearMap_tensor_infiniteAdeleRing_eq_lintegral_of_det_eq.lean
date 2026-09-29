-- Prove2me | Theorems.Thm_AutomorphicForm_prod_norm_pow_mult_mul_lintegral_comp_linearMap_tensor_infiniteAdeleRing_eq_lintegral_of_det_eq
-- name    : AutomorphicForm.prod_norm_pow_mult_mul_lintegral_comp_linearMap_tensor_infiniteAdeleRing_eq_lintegral_of_det_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/e438c799-825b-5186-97b9-e7def2306ec2
-- title:
--   Archimedean modulus of a K_∞-linear map on L⊗_K K_∞
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a finite extension of $K$, and let $K_\infty$ denote the infinite adele ring `InfiniteAdeleRing K`. Equip $E = L \otimes_K K_\infty$ with a measurable space structure which is the Borel structure of its topology, and let $\lambda$ be an additive Haar measure on $E$. Let $T : E \to E$ be a $K_\infty$-linear endomorphism, let $d$ be a unit of $K_\infty$, and assume $\det_{K_\infty} T = d$. Let $G : E \to [0,\infty]$ be measurable. Then
--   $$\Big(\prod_{v} \lVert d_v\rVert^{\,m_v}\Big)\int_E^{-} G(T\xi)\,\mathrm d\lambda(\xi) = \int_E^{-} G\,\mathrm d\lambda,$$
--   where the product is over the infinite places $v$ of $K$, $d_v$ is the component of $d$ at $v$, $m_v =$ `v.mult` is the local multiplicity ($1$ for a real place, $2$ for a complex one), and the positive real factor is transported to $[0,\infty]$ via `ENNReal.ofReal`. The integrals are lower Lebesgue integrals of $[0,\infty]$-valued functions.
--
--   This is the archimedean module (modulus of distension) of a $K_\infty$-linear map on the finite free $K_\infty$-module $L \otimes_K K_\infty$: its determinant acts on additive Haar measure through the idelic norm $\prod_{v\mid\infty}\lVert\cdot\rVert_v^{m_v}$. It is used in the archimedean change-of-variable computations for integrals of automorphic forms, and is cited by [`AutomorphicForm.prod_norm_one_sub_norm_pow_mult_mul_lintegral_comp_sigmaTensor_sub_mul_eq_lintegral`](thm.html#AutomorphicForm.prod_norm_one_sub_norm_pow_mult_mul_lintegral_comp_sigmaTensor_sub_mul_eq_lintegral).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_prod_norm_pow_mult_mul_lintegral_comp_linearMap_tensor_infiniteAdeleRing_eq_lintegral_of_det_eq.lean

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

theorem AutomorphicForm.prod_norm_pow_mult_mul_lintegral_comp_linearMap_tensor_infiniteAdeleRing_eq_lintegral_of_det_eq
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    [MeasurableSpace (L ⊗[K] InfiniteAdeleRing K)] [BorelSpace (L ⊗[K] InfiniteAdeleRing K)]
    (lam : Measure (L ⊗[K] InfiniteAdeleRing K)) [lam.IsAddHaarMeasure]
    (T : (L ⊗[K] InfiniteAdeleRing K) →ₗ[InfiniteAdeleRing K] (L ⊗[K] InfiniteAdeleRing K))
    (d : (InfiniteAdeleRing K)ˣ) (hT : LinearMap.det T = (d : InfiniteAdeleRing K))
    (G : (L ⊗[K] InfiniteAdeleRing K) → ℝ≥0∞) (hG : Measurable G) :
    ENNReal.ofReal (∏ v : InfinitePlace K, ‖(d : InfiniteAdeleRing K) v‖ ^ v.mult) * ∫⁻ ξ, G (T ξ) ∂lam =
      ∫⁻ ξ, G ξ ∂lam := by sorry

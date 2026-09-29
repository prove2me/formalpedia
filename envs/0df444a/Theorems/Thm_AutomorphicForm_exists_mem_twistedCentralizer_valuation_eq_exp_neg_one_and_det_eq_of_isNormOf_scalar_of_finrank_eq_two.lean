-- Prove2me | Theorems.Thm_AutomorphicForm_exists_mem_twistedCentralizer_valuation_eq_exp_neg_one_and_det_eq_of_isNormOf_scalar_of_finrank_eq_two
-- name    : AutomorphicForm.exists_mem_twistedCentralizer_valuation_eq_exp_neg_one_and_det_eq_of_isNormOf_scalar_of_finrank_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/fd69b3f8-b375-57ac-b96e-a59223b42299
-- title:
--   Uniformiser determinant in a twisted centralizer of GL₂
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra of degree $\operatorname{finrank}_K L = 2$, and let $\sigma$ be a $K$-algebra automorphism of $L$ such that every $K$-algebra automorphism of $L$ lies in the subgroup of integer powers of $\sigma$. Let $v$ be a height-one prime of the ring of integers $\mathcal{O}_K$, write $K_v$ for the associated adic completion `v.adicCompletion K`, let $c$ be a unit of $K_v$, and let $\delta \in \mathrm{GL}_2(L \otimes_K K_v)$. Assume that $\delta$ satisfies [`AutomorphicForm.IsNormOf`](def/AutomorphicForm_TwistedOrbital.html#L217) with respect to the scalar matrix $\mathrm{diag}(c,c)$, that is: there is $y \in \mathrm{GL}_2(L \otimes_K K_v)$ for which the image of $\mathrm{diag}(c,c)$ under the base-change map $\mathrm{GL}_2(K_v) \to \mathrm{GL}_2(L \otimes_K K_v)$ equals $y^{-1} \cdot \mathrm{normString}\,K\,L\,K_v\,\sigma\,\delta \cdot y$, where the norm string is the product built from $\delta$ and its $\sigma$-twists. The conclusion asserts the existence of an element $t$ of the $\sigma$-twisted centralizer of $\delta$, i.e. of the subgroup of those $t \in \mathrm{GL}_2(L \otimes_K K_v)$ with $t\,\delta\,(\sigma_{\mathrm{GL}} t)^{-1} = \delta$, where $\sigma_{\mathrm{GL}}$ acts entrywise by `sigmaTensor K L K_v σ`, together with a unit $s$ of $K_v$ whose valuation equals $\exp(-1)$, such that $\det t$ is the image of $s$ under the unit map induced by $\mathrm{includeRight} : K_v \to L \otimes_K K_v$, $a \mapsto 1 \otimes a$.
--
--   In classical terms, the twisted centralizer of a $\delta$ whose norm string is conjugate to a central element is the group of units of a quaternion algebra over $K_v$ split by $L \otimes_K K_v$, whose determinant on this group is the reduced norm; the statement is the existence of an element of reduced norm of valuation exactly one, a form of surjectivity of the reduced norm onto $K_v^\times$. It is used in the comparison of volumes of pieces of the twisted centralizer cut out by the valuation of the determinant, and in the evaluation of twisted orbital integrals occurring in the quadratic base change for $\mathrm{GL}_2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_mem_twistedCentralizer_valuation_eq_exp_neg_one_and_det_eq_of_isNormOf_scalar_of_finrank_eq_two.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_mem_twistedCentralizer_valuation_eq_exp_neg_one_and_det_eq_of_isNormOf_scalar_of_finrank_eq_two
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : HeightOneSpectrum (𝓞 K))
    (c : (v.adicCompletion K)ˣ)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hδ : AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ) :
    ∃ t ∈ AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ,
      ∃ s : (v.adicCompletion K)ˣ, Valued.v (s : v.adicCompletion K) = WithZero.exp (-1) ∧
        Matrix.GeneralLinearGroup.det t =
          Units.map (Algebra.TensorProduct.includeRight :
            v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K).toRingHom.toMonoidHom s := by sorry

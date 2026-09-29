-- Prove2me | Theorems.Thm_AutomorphicForm_exists_nhds_isCompact_forall_twistedCentralizer_conjAe_mul_mem_of_neg
-- name    : AutomorphicForm.exists_nhds_isCompact_forall_twistedCentralizer_conjAe_mul_mem_of_neg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/9b5e37c2-b531-5f38-a562-9fd7bed8c4d9
-- title:
--   Uniform properness of twisted conjugation near a negative scalar norm
-- statement:
--   Work with $K=\mathbb{R}$, $L=\mathbb{C}$, $A=\mathbb{R}$ and $\sigma$ the complex conjugation $\mathbb{R}$-algebra automorphism of $\mathbb{C}$, so that the relevant group is $\mathrm{GL}_2(\mathbb{C}\otimes_{\mathbb{R}}\mathbb{R})$ and `sigmaGL` is the group endomorphism induced entrywise by $\sigma\otimes\mathrm{id}$. Let $c$ be a unit of $\mathbb{R}$ with $c<0$, and let $\delta,y\in\mathrm{GL}_2(\mathbb{C}\otimes_{\mathbb{R}}\mathbb{R})$ satisfy `IsNormConjugator`, i.e. the image of the scalar matrix $c\cdot 1$ under the base-change homomorphism $\mathrm{GL}_2(\mathbb{R})\to\mathrm{GL}_2(\mathbb{C}\otimes_{\mathbb{R}}\mathbb{R})$ equals $y^{-1}\bigl(\prod_{i<\operatorname{finrank}_{\mathbb{R}}\mathbb{C}}\sigma^{i}(\delta)\bigr)y$; since $\operatorname{finrank}_{\mathbb{R}}\mathbb{C}=2$ this norm string is $\delta\,\sigma(\delta)$. Let $\omega$ be a compact subset of $\mathrm{GL}_2(\mathbb{C}\otimes_{\mathbb{R}}\mathbb{R})$. The assertion is that there exist a neighbourhood $U_1$ of the identity and a compact set $\Omega$ such that for every $h\in U_1$ lying in the twisted centraliser of $\delta$, that is with $h\,\delta\,\sigma(h)^{-1}=\delta$, and every $x$ with $x^{-1}(h\delta)\,\sigma(x)\in\omega$, one can write $x=t\,d$ with $t$ in that twisted centraliser and $d\in\Omega$.
--
--   This is the archimedean, second-kind case of the uniform properness of the twisted conjugation maps $x\mapsto x^{-1}(h\delta)\sigma(x)$ for $h$ ranging over a small neighbourhood of $1$ in the twisted centraliser of $\delta$: compactness of the image forces $x$ to lie in a fixed compact set modulo the twisted centraliser, uniformly in $h$. It underlies the construction of twisted section functions and the continuity and limit behaviour of twisted orbital integrals at the real place, and is used by [`AutomorphicForm.exists_isTwistedSectionFnOn_and_continuous_completion_of_not_isSigmaConjugate_scalar_of_finrank_eq_two`](thm.html#AutomorphicForm.exists_isTwistedSectionFnOn_and_continuous_completion_of_not_isSigmaConjugate_scalar_of_finrank_eq_two) and [`AutomorphicForm.exists_pos_forall_tendsto_isTwistedOrbitalIntegralOn_mul_nhdsGT_conjAe_of_neg_of_inf_twistedCentralizer`](thm.html#AutomorphicForm.exists_pos_forall_tendsto_isTwistedOrbitalIntegralOn_mul_nhdsGT_conjAe_of_neg_of_inf_twistedCentralizer).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_nhds_isCompact_forall_twistedCentralizer_conjAe_mul_mem_of_neg.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_nhds_isCompact_forall_twistedCentralizer_conjAe_mul_mem_of_neg
    (c : ℝˣ) (hc : (c : ℝ) < 0)
    (δ y : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (hδ : IsNormConjugator ℝ ℂ ℝ Complex.conjAe (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y)
    (ω : Set (GL (Fin 2) (ℂ ⊗[ℝ] ℝ))) (hω : IsCompact ω) :
    ∃ U₁ ∈ nhds (1 : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)),
      ∃ Ω : Set (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)), IsCompact Ω ∧
      ∀ h ∈ U₁, h ∈ twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ →
        ∀ x : GL (Fin 2) (ℂ ⊗[ℝ] ℝ),
          x⁻¹ * (h * δ) * sigmaGL ℝ ℂ ℝ Complex.conjAe x ∈ ω →
            ∃ t ∈ twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ, ∃ d ∈ Ω, x = t * d := by sorry

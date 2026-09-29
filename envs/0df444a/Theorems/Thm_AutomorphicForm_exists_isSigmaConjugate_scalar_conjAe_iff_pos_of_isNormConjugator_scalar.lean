-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isSigmaConjugate_scalar_conjAe_iff_pos_of_isNormConjugator_scalar
-- name    : AutomorphicForm.exists_isSigmaConjugate_scalar_conjAe_iff_pos_of_isNormConjugator_scalar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/01f4e1a1-0f5c-57cf-a5db-b25f97aec700
-- title:
--   Scalar σ-conjugacy at a real place holds iff c>0
-- statement:
--   Fix a unit $c \in \mathbb{R}^\times$ and two elements $\delta, y \in \mathrm{GL}_2(\mathbb{C} \otimes_{\mathbb{R}} \mathbb{R})$, and write $\sigma$ for the automorphism of $\mathrm{GL}_2(\mathbb{C} \otimes_{\mathbb{R}} \mathbb{R})$ obtained by applying entrywise the ring automorphism of $\mathbb{C} \otimes_{\mathbb{R}} \mathbb{R}$ induced by complex conjugation `Complex.conjAe` on the left factor and the identity on the right. Assume that $y$ exhibits the scalar matrix $c \cdot 1 \in \mathrm{GL}_2(\mathbb{R})$, transported into $\mathrm{GL}_2(\mathbb{C} \otimes_{\mathbb{R}} \mathbb{R})$ along the inclusion of the right tensor factor, as a conjugate of the norm string of $\delta$: that is, the image of $c \cdot 1$ equals $y^{-1} \bigl(\prod_{i < [\mathbb{C} : \mathbb{R}]} \sigma^i(\delta)\bigr) y$, the product being $\delta \cdot \sigma(\delta)$ since $[\mathbb{C} : \mathbb{R}] = 2$. The assertion is an equivalence: there exists a unit $z \in (\mathbb{C} \otimes_{\mathbb{R}} \mathbb{R})^\times$ and an $x \in \mathrm{GL}_2(\mathbb{C} \otimes_{\mathbb{R}} \mathbb{R})$ with $z \cdot 1 = x^{-1} \delta \, \sigma(x)$ — i.e. $\delta$ is $\sigma$-conjugate to a scalar matrix — if and only if the real number underlying $c$ is strictly positive.
--
--   This is the kind–sign dictionary at a real place lying under a complex place: in Langlands' terminology for the central twisted classes of $\mathrm{GL}_2$, the twisted classes of the first kind are exactly those whose central norm invariant $c$ is positive, the negative $c$ giving the second kind. It is used to split the analysis of twisted orbital integrals into the two kinds, being cited by [`AutomorphicForm.exists_isTwistedSectionFnOn_and_continuous_completion_of_not_isSigmaConjugate_scalar_of_finrank_eq_two`](thm.html#AutomorphicForm.exists_isTwistedSectionFnOn_and_continuous_completion_of_not_isSigmaConjugate_scalar_of_finrank_eq_two) and by [`AutomorphicForm.twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom`](thm.html#AutomorphicForm.twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isSigmaConjugate_scalar_conjAe_iff_pos_of_isNormConjugator_scalar.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_isSigmaConjugate_scalar_conjAe_iff_pos_of_isNormConjugator_scalar
    (c : ℝˣ) (δ y : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (hδ : IsNormConjugator ℝ ℂ ℝ Complex.conjAe (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y) :
    (∃ z : (ℂ ⊗[ℝ] ℝ)ˣ, IsSigmaConjugate ℝ ℂ ℝ Complex.conjAe δ (Matrix.GeneralLinearGroup.scalar (Fin 2) z)) ↔
      0 < (c : ℝ) := by sorry

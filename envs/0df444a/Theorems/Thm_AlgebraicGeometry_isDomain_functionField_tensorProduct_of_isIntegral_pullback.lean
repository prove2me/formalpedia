-- Prove2me | Theorems.Thm_AlgebraicGeometry_isDomain_functionField_tensorProduct_of_isIntegral_pullback
-- name    : AlgebraicGeometry.isDomain_functionField_tensorProduct_of_isIntegral_pullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/d3ac89e1-0c38-5bbe-8b42-9d518fb9242c
-- title:
--   Function field tensor C is a domain for integral pullback
-- statement:
--   Fix a natural number $M$ that is nonzero, and write $R = \mathbb{Z}[1/M]$ for the localisation of $\mathbb{Z}$ away from the image of $M$ in $\mathbb{Z}$. Let $X$ be a scheme (with data in the base universe) that is integral, equipped with a morphism $\pi_X : X \to \operatorname{Spec} R$, and let $C$ be a field, algebraically closed and of characteristic zero, equipped with a morphism $s_C : \operatorname{Spec} C \to \operatorname{Spec} R$ of schemes; no compatibility between $\pi_X$ and $s_C$ beyond the common target is assumed, and the usual typeclass data for these objects are understood. Assume that the fibre product of $\pi_X$ and $s_C$, taken in the category of schemes, is integral. The conclusion asserts the existence of a proof that the function field $X.\mathrm{functionField}$, that is the residue field of $X$ at its generic point, has characteristic zero, and, with the resulting $\mathbb{Q}$-algebra structure, that the tensor product $X.\mathrm{functionField} \otimes_{\mathbb{Q}} C$ is an integral domain (in particular nontrivial, with no zero divisors).
--
--   This is the scheme-theoretic half of a statement about geometric integrality under base change: integrality of $X \times_{\operatorname{Spec}\mathbb{Z}[1/M]} \operatorname{Spec} C$ forces $K(X)$ to be of characteristic zero and $K(X) \otimes_{\mathbb{Q}} C$ to be a domain. It feeds [`AlgebraicGeometry.functionField_mem_range_algebraMap_rat_of_isAlgebraic_of_isIntegral_pullback`](thm.html#AlgebraicGeometry.functionField_mem_range_algebraMap_rat_of_isAlgebraic_of_isIntegral_pullback), where the domain property is used to show that elements of $K(X)$ algebraic over $\mathbb{Q}$ already lie in the image of $\mathbb{Q}$; characteristic zero of the function field is obtained from [`AlgebraicGeometry.charZero_functionField_of_hom_spec_of_charZero`](thm.html#AlgebraicGeometry.charZero_functionField_of_hom_spec_of_charZero), which deduces it from a morphism $\operatorname{Spec} C \to X$ with $C$ a characteristic-zero field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isDomain_functionField_tensorProduct_of_isIntegral_pullback.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.isDomain_functionField_tensorProduct_of_isIntegral_pullback
    (M : ℕ) [NeZero M]
    (X : Scheme.{0}) [IsIntegral X] (πX : X ⟶ Spec (CommRingCat.of (Localization.Away ((M : ℕ) : ℤ))))
    (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (sC : Spec (CommRingCat.of C) ⟶ Spec (CommRingCat.of (Localization.Away ((M : ℕ) : ℤ))))
    (hC : IsIntegral (CategoryTheory.Limits.pullback πX sC)) :
    ∃ hchar : CharZero X.functionField, haveI := hchar;
      IsDomain (X.functionField ⊗[ℚ] C) := by sorry

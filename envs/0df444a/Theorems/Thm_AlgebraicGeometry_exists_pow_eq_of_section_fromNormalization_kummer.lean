-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_pow_eq_of_section_fromNormalization_kummer
-- name    : AlgebraicGeometry.exists_pow_eq_of_section_fromNormalization_kummer
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/39e57f7d-bcd0-5723-a297-2ea7c2fc3700
-- title:
--   Splitting of a Kummer normalisation gives a k-th root
-- statement:
--   Let $X$ be an integral scheme, with function field $K(X)$ (in Mathlib, `X.functionField`, the stalk of $X$ at its generic point), let $k$ be a natural number and let $g \in K(X)$ be non-zero. Consider the morphism obtained by composing $\operatorname{Spec}$ of the structure map $K(X) \to K(X)[T]/(T^k - g)$, where the target is written as `AdjoinRoot (Polynomial.X ^ k - Polynomial.C g)`, with the canonical morphism `X.fromSpecStalk (genericPoint X) : Spec K(X) ⟶ X`; thus a morphism $\operatorname{Spec}\bigl(K(X)[T]/(T^k-g)\bigr) \to X$. Let `s` be a morphism from $X$ to the normalisation of $X$ in this morphism (Mathlib's `Scheme.Hom.normalization`), and assume that `s` followed by the induced morphism `fromNormalization` from that normalisation to $X$ is the identity of $X$, i.e. `s` is a section of the normalisation morphism. The conclusion is that there exists $f \in K(X)$ with $f^k = g$. No assumption is made that $k$ is invertible on $X$, nor that $k$ is positive.
--
--   This is the statement that a Kummer covering of an integral scheme, realised as the relative normalisation of $X$ in $K(X)[T]/(T^k-g)$, can only be split by a section when $g$ is already a $k$-th power in the function field; restricting the section to the generic point gives a $K(X)$-algebra map $K(X)[T]/(T^k-g) \to K(X)$, and the image of $T$ is the required root. It is used at the end of the kernel-of-reduction arguments for Picard groups of semistable models, in [`AlgebraicCurve.mem_principal_of_zsmul_mem_principal_of_forall_mapDomain_placeMap_eq_zero_of_genusFF_of_semistableModel_of_descent`](thm.html#AlgebraicCurve.mem_principal_of_zsmul_mem_principal_of_forall_mapDomain_placeMap_eq_zero_of_genusFF_of_semistableModel_of_descent) and [`AlgebraicCurve.sum_mem_principal_of_zsmul_mem_principal_of_isNodalPrincipal_mapDomain_placeMap_of_semistableModel_of_descent`](thm.html#AlgebraicCurve.sum_mem_principal_of_zsmul_mem_principal_of_isNodalPrincipal_mapDomain_placeMap_of_semistableModel_of_descent), where a Kummer cover split over a fibre is shown to force the relevant function to be a $k$-th power.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_pow_eq_of_section_fromNormalization_kummer.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry Polynomial

theorem AlgebraicGeometry.exists_pow_eq_of_section_fromNormalization_kummer
    {X : Scheme.{u}} [IsIntegral X] (k : ℕ) (g : X.functionField) (hg : g ≠ 0)
    (s : X ⟶ (Spec.map (CommRingCat.ofHom (algebraMap X.functionField
        (AdjoinRoot (Polynomial.X ^ k - Polynomial.C g : Polynomial X.functionField)))) ≫
      X.fromSpecStalk (genericPoint X)).normalization)
    (hs : s ≫ (Spec.map (CommRingCat.ofHom (algebraMap X.functionField
        (AdjoinRoot (Polynomial.X ^ k - Polynomial.C g : Polynomial X.functionField)))) ≫
      X.fromSpecStalk (genericPoint X)).fromNormalization = 𝟙 X) :
    ∃ f : X.functionField, f ^ k = g := by sorry

-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_algEquiv_tensorProduct_functionField_pullback_of_isAlgebraic
-- name    : AlgebraicGeometry.exists_algEquiv_tensorProduct_functionField_pullback_of_isAlgebraic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/249c468a-583e-54d0-ad67-8395d8117fa4
-- title:
--   Function field of a base change along an algebraic extension
-- statement:
--   Let $K$ be a field, $K'$ a field equipped with a $K$-algebra structure such that $K'/K$ is algebraic, and let $x \colon X \to \operatorname{Spec} K$ be a morphism of schemes with $X$ integral; assume moreover that the pullback $X' := X \times_{\operatorname{Spec} K} \operatorname{Spec} K'$ along $\operatorname{Spec}$ of the structure map $K \to K'$ is integral. The function field $X.\mathtt{functionField}$ (the stalk at the generic point) is regarded as a $K$-algebra via `baseToFunctionField` applied to $x$, that is, via the ring map obtained from $x$ on global sections, composed with the germ map at the generic point; likewise the function field of $X'$ is regarded as a $K'$-algebra via `baseToFunctionField` applied to the second projection $X' \to \operatorname{Spec} K'$. The assertion is that there exists an isomorphism of $K'$-algebras $\Phi \colon K' \otimes_K X.\mathtt{functionField} \to (X').\mathtt{functionField}$ such that, for every open $U \subseteq X$ whose associated scheme is nonempty and whose preimage under the first projection $\pi \colon X' \to X$ is also nonempty as a scheme, and every section $s \in \Gamma(X, U)$, one has $\Phi(1 \otimes s_\eta) = (\pi^{*}s)_{\eta'}$, where $s_\eta$ is the germ of $s$ at the generic point of $X$ and $(\pi^{*}s)_{\eta'}$ is the germ at the generic point of $X'$ of the pullback of $s$ along $\pi$ over $\pi^{-1}(U)$.
--
--   This is the base-change formula $K(X \times_K K') \cong K' \otimes_K K(X)$ for an algebraic extension $K'/K$, in the form of a $K'$-algebra isomorphism normalised by its effect on germs of regular functions. It is used in the construction of curve models over base-changed fields, for instance in the Čeredník–Drinfel'd setting and in the comparison of function fields of modular curves under base change.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_algEquiv_tensorProduct_functionField_pullback_of_isAlgebraic.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
open scoped TensorProduct

theorem AlgebraicGeometry.exists_algEquiv_tensorProduct_functionField_pullback_of_isAlgebraic
    {K : Type u} [Field K] (K' : Type u) [Field K'] [Algebra K K'] [Algebra.IsAlgebraic K K']
    {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K)) [IsIntegral X]
    [IsIntegral ↑(pullback x (Spec.map (CommRingCat.ofHom (algebraMap K K'))))] :
    letI := (baseToFunctionField x).toAlgebra
    letI := (baseToFunctionField
      (pullback.snd x (Spec.map (CommRingCat.ofHom (algebraMap K K'))))).toAlgebra
    ∃ Φ : K' ⊗[K] X.functionField ≃ₐ[K']
        (pullback x (Spec.map (CommRingCat.ofHom (algebraMap K K')))).functionField,
      ∀ (U : X.Opens) [hU : Nonempty (U : Scheme.{u})]
        [hU' : Nonempty (((pullback.fst x (Spec.map (CommRingCat.ofHom (algebraMap K K')))) ⁻¹ᵁ U : (pullback x (Spec.map (CommRingCat.ofHom (algebraMap K K')))).Opens) : Scheme.{u})]
        (s : Γ(X, U)),
        Φ (1 ⊗ₜ X.germToFunctionField U s) =
          (pullback x (Spec.map (CommRingCat.ofHom (algebraMap K K')))).germToFunctionField
            ((pullback.fst x (Spec.map (CommRingCat.ofHom (algebraMap K K')))) ⁻¹ᵁ U)
            ((pullback.fst x (Spec.map (CommRingCat.ofHom (algebraMap K K')))).app U s) := by sorry

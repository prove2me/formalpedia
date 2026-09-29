-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_algHom_tensorProduct_functionField_pullback_injective_isFractionRing
-- name    : AlgebraicGeometry.exists_algHom_tensorProduct_functionField_pullback_injective_isFractionRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/7f12bed3-c696-5580-940f-23966c96ca23
-- title:
--   Function field of a base change: K(X') = Frac(K' ⊗_K K(X))
-- statement:
--   Let $K$ and $K'$ be fields with $K'$ a $K$-algebra, let $X$ be a scheme and $x \colon X \to \operatorname{Spec} K$ a morphism, and assume that $X$ is integral and that the fibre product $X' := X \times_{\operatorname{Spec} K} \operatorname{Spec} K'$, formed along the morphism $\operatorname{Spec} K' \to \operatorname{Spec} K$ induced by $K \to K'$, is integral as well. Give $X.\mathrm{functionField}$ the $K$-algebra structure coming from the ring map [`AlgebraicCurve.baseToFunctionField`](def/AlgebraicCurve_CurveModel.html#L18) attached to $x$, i.e. the composite of the inverse of the $\Gamma$–$\operatorname{Spec}$ adjunction isomorphism for $K$, the map on global sections induced by $x$, and the germ at the generic point; similarly give $X'.\mathrm{functionField}$ the $K'$-algebra structure obtained the same way from the second projection $X' \to \operatorname{Spec} K'$. Then there exists a $K'$-algebra homomorphism $\Phi \colon K' \otimes_K X.\mathrm{functionField} \to X'.\mathrm{functionField}$ such that: $\Phi$ is injective; regarding $X'.\mathrm{functionField}$ as an algebra over $K' \otimes_K X.\mathrm{functionField}$ via $\Phi$, it is a fraction ring (localisation at the non-zero-divisors) of $K' \otimes_K X.\mathrm{functionField}$; and for every open $U \subseteq X$ such that both $U$ and its preimage under the first projection $\mathrm{pr}_1 \colon X' \to X$ are non-empty as schemes, and every $s \in \Gamma(X, U)$, one has $\Phi(1 \otimes s_{\mathrm{germ}}) = (\mathrm{pr}_1^{*} s)_{\mathrm{germ}}$, where the germs are taken at the respective generic points, of $s$ on $U$ and of the pullback of $s$ along $\mathrm{pr}_1$ on $\mathrm{pr}_1^{-1} U$.
--
--   This is the base-change description of the function field of an integral scheme over a field: $K(X')$ is the fraction field of $K' \otimes_K K(X)$, compatibly with germs of sections on opens, for an arbitrary field extension $K \subseteq K'$ under the assumption that the base change remains integral. It is used to compare generators and linear independence in $K(X')$ over $K(X)$, and in the construction of curve models and function fields for modular curves over extended base fields.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_algHom_tensorProduct_functionField_pullback_injective_isFractionRing.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
open scoped TensorProduct

theorem AlgebraicGeometry.exists_algHom_tensorProduct_functionField_pullback_injective_isFractionRing
    {K : Type u} [Field K] (K' : Type u) [Field K'] [Algebra K K']
    {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K)) [IsIntegral X]
    [IsIntegral ↑(pullback x (Spec.map (CommRingCat.ofHom (algebraMap K K'))))] :
    letI := (baseToFunctionField x).toAlgebra
    letI := (baseToFunctionField
      (pullback.snd x (Spec.map (CommRingCat.ofHom (algebraMap K K'))))).toAlgebra
    ∃ Φ : K' ⊗[K] X.functionField →ₐ[K']
        (pullback x (Spec.map (CommRingCat.ofHom (algebraMap K K')))).functionField,
      Function.Injective Φ ∧
      (letI := Φ.toRingHom.toAlgebra
       IsFractionRing (K' ⊗[K] X.functionField)
         (pullback x (Spec.map (CommRingCat.ofHom (algebraMap K K')))).functionField) ∧
      ∀ (U : X.Opens) [hU : Nonempty (U : Scheme.{u})]
        [hU' : Nonempty (((pullback.fst x (Spec.map (CommRingCat.ofHom (algebraMap K K')))) ⁻¹ᵁ U : (pullback x (Spec.map (CommRingCat.ofHom (algebraMap K K')))).Opens) : Scheme.{u})]
        (s : Γ(X, U)),
        Φ (1 ⊗ₜ X.germToFunctionField U s) =
          (pullback x (Spec.map (CommRingCat.ofHom (algebraMap K K')))).germToFunctionField
            ((pullback.fst x (Spec.map (CommRingCat.ofHom (algebraMap K K')))) ⁻¹ᵁ U)
            ((pullback.fst x (Spec.map (CommRingCat.ofHom (algebraMap K K')))).app U s) := by sorry

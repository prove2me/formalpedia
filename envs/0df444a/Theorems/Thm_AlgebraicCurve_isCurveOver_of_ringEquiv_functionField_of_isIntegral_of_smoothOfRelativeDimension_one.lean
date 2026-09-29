-- Prove2me | Theorems.Thm_AlgebraicCurve_isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
-- name    : AlgebraicCurve.isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/2a07ed1f-2627-5705-acfa-19b1fb2bc410
-- title:
--   Function fields of smooth integral curves over K
-- statement:
--   Let $K$ be a field, let $F$ be a field equipped with a $K$-algebra structure, and let $C$ be a scheme with a morphism $c : C \to \operatorname{Spec} K$ such that $C$ is integral and $c$ is smooth of relative dimension $1$. Suppose given a ring isomorphism $\varphi : F \xrightarrow{\sim} \mathcal{K}(C)$ onto the function field of $C$ (the stalk of the structure sheaf at the generic point) which is compatible with the $K$-structures, in the sense that for every $a \in K$ one has $\varphi(a \cdot 1) =$ `baseToFunctionField c a`, the image of $a$ under $K \cong \Gamma(\operatorname{Spec} K, \mathcal{O}) \to \Gamma(C, \mathcal{O}_C) \to \mathcal{K}(C)$. Then $F$ satisfies `IsCurveOver K F`, that is: (i) for every place of $F$ over $K$ — a valuation subring of $F$ containing the image of $K$, distinct from $F$ itself, and a principal ideal ring — the residue field is a finite-dimensional $K$-vector space; (ii) for every $f \in F$ with $f \neq 0$ there is a divisor $D$ whose value at each place $v$ is $v.\mathrm{ord}(f)$ and whose degree is $0$; and (iii) the module of Kähler differentials $\Omega_{F/K}$ is free of rank $1$ over $F$.
--
--   This is the bridge from the scheme-theoretic input (an integral scheme smooth of relative dimension one over $\operatorname{Spec} K$) to the axiomatic package of a one-variable function field over $K$ used throughout the project's divisor and Riemann–Roch theory; no properness of $c$ and no perfectness of $K$ is assumed. It is invoked by the results on curve models and on orders at places, which work with a smooth model and need its function field to be a curve field over $K$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one.lean

import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_CurveModel
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory AlgebraicGeometry AlgebraicCurve

theorem AlgebraicCurve.isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
    {K : Type u} [Field K] {F : Type v} [Field F] [Algebra K F]
    {C : Scheme.{u}} (c : C ⟶ Spec (.of K)) [IsIntegral C]
    [SmoothOfRelativeDimension 1 c] (φ : F ≃+* C.functionField)
    (hφ : ∀ a : K, φ (algebraMap K F a) = baseToFunctionField c a) :
    IsCurveOver K F := by sorry

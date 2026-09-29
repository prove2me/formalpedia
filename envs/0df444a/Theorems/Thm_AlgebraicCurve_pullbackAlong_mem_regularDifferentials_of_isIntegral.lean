-- Prove2me | Theorems.Thm_AlgebraicCurve_pullbackAlong_mem_regularDifferentials_of_isIntegral
-- name    : AlgebraicCurve.pullbackAlong_mem_regularDifferentials_of_isIntegral
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/c7df6692-25bb-5dad-8fe0-76c96da547dd
-- title:
--   Integral pull-back preserves regular differentials
-- statement:
--   Let $K$ be a perfect field and let $F$, $F'$ be fields equipped with $K$-algebra structures, each satisfying `IsCurveOver K F` (respectively `IsCurveOver K F'`): every nonzero element has a principal divisor of degree $0$, every place has residue field finite over $K$, and the module of Kähler differentials $\Omega[F\,/\,K]$ is free of rank $1$ over the field itself. Here a place of $F$ over $K$ is a valuation subring of $F$ that contains the image of $K$, is not all of $F$, and is a principal ideal ring. Assume in addition that $F'$ is essentially of finite type over $K$, and that for every place $v$ of $F$ and every place $w$ of $F'$ the element $v.\mathrm{dCoord} = \mathrm{d}(v.\mathrm{uniformizer})$, respectively $w.\mathrm{dCoord}$, spans the whole differential module over the field (the hypothesis `DCoordGenerates`). Let $\varphi : F \to F'$ be a $K$-algebra homomorphism whose underlying ring homomorphism is integral, i.e. every element of $F'$ is integral over the image of $\varphi$. Let $\omega \in \Omega[F\,/\,K]$ be regular, meaning that for every place $v$ of $F$ there is $f$ in the valuation subring of $v$ with $\omega = f \cdot v.\mathrm{dCoord}$. Then the pull-back of $\omega$, the image of $\omega$ under `KaehlerDifferential.map` for the $F$-algebra structure on $F'$ given by $\varphi$, viewed $K$-linearly, is again regular: at every place $w$ of $F'$ it is a $w$-integral multiple of $w.\mathrm{dCoord}$.
--
--   This is the statement that differentials of the first kind pull back to differentials of the first kind along an integral map of one-variable function fields over a perfect field, the function-field form of the fact that global sections of the sheaf of differentials pull back along a finite morphism of curves. It is used in the comparison of differentials on modular curves under degeneracy maps and Hecke correspondences, where it feeds into [`ModularCurve.kaehlerToFunctionField_eq_correspondence_degeneracyRoof_of_res_eq_heckeDiffBar`](thm.html#ModularCurve.kaehlerToFunctionField_eq_correspondence_degeneracyRoof_of_res_eq_heckeDiffBar).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_pullbackAlong_mem_regularDifferentials_of_isIntegral.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_AlgebraicCurve_DifferentialPushPull
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AlgebraicCurve.pullbackAlong_mem_regularDifferentials_of_isIntegral
    {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [PerfectField K] [AlgebraicCurve.IsCurveOver K F] [AlgebraicCurve.IsCurveOver K F'] [Algebra.EssFiniteType K F']
    [∀ v : AlgebraicCurve.Place K F, v.DCoordGenerates] [∀ w : AlgebraicCurve.Place K F', w.DCoordGenerates]
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    {ω : Ω[F⁄K]} (hω : ω ∈ AlgebraicCurve.regularDifferentials K F) :
    AlgebraicCurve.Differential.pullbackAlong φ ω ∈ AlgebraicCurve.regularDifferentials K F' := by sorry

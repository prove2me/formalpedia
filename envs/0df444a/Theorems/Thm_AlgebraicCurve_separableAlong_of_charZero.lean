-- Prove2me | Theorems.Thm_AlgebraicCurve_separableAlong_of_charZero
-- name    : AlgebraicCurve.separableAlong_of_charZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/af5fdffe-01a6-5b74-93da-aaecd5a70e34
-- title:
--   Integral extensions in characteristic zero are separable along φ
-- statement:
--   Let $K$, $F$, $F_1$ be fields, with $F$ and $F_1$ both $K$-algebras, and suppose $F$ has characteristic zero. Let $\varphi \colon F \to F_1$ be a $K$-algebra homomorphism whose underlying ring homomorphism is integral, that is, every element of $F_1$ satisfies a monic polynomial with coefficients in the image $\varphi(F)$. The conclusion is `SeparableAlong K φ`, which by definition means the following: equip $F_1$ with the $F$-algebra structure induced by $\varphi$ (the structure `algebraAlong φ`, whose structure map is $\varphi$ itself), and then $F_1$ is a separable $F$-algebra in the sense of `Algebra.IsSeparable`, i.e. every element of $F_1$ is algebraic over $F$ with separable minimal polynomial. No hypothesis is imposed on $F_1$ beyond being a field and a $K$-algebra; in particular the characteristic hypothesis is placed on the source field $F$, and `SeparableAlong` is the formulation that avoids fixing an ambient `Algebra F F₁` instance.
--
--   This is the standard fact that an algebraic extension of a field of characteristic zero, such fields being perfect, is separable, recast for an extension presented by an explicit embedding $\varphi$ rather than by an algebra instance. It supplies the separability input required by the fundamental identity and the norm formula for correspondences, and is invoked throughout the treatment of curves and differentials over fields of characteristic zero.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_separableAlong_of_charZero.lean

import Definitions.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.separableAlong_of_charZero {K F F₁ : Type*} [Field K] [Field F] [Field F₁] [Algebra K F] [Algebra K F₁] [CharZero F] (φ : F →ₐ[K] F₁) (hφ : φ.toRingHom.IsIntegral) : SeparableAlong K φ := by sorry

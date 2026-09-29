-- Prove2me | Theorems.Thm_AlgebraicCurve_pullbackAlong_mem_regularDifferentials_of_mem_of_isCurveOver
-- name    : AlgebraicCurve.pullbackAlong_mem_regularDifferentials_of_mem_of_isCurveOver
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/b41191f0-ab58-5357-9554-75e386eadfe4
-- title:
--   Automorphisms preserve regular differentials on a curve
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, $K$ perfect and $F$ essentially of finite type over $K$, and assume [`AlgebraicCurve.IsCurveOver K F`](def/AlgebraicCurve_IsCurveOver.html#L15): every nonzero $f \in F$ has a divisor, i.e. a finitely supported integer-valued function on the places $v$ of $F/K$ (a place being a valuation subring of $F$ containing $K$, distinct from $F$ and a principal ideal ring) whose value at each $v$ is $\operatorname{ord}_v f$ and whose degree is $0$; every residue field $\kappa(v)$ is finite-dimensional over $K$; and $\Omega_{F/K}$ is free of rank one over $F$. Assume moreover that for every place $v$ the differential $\mathrm{d}C_v := \mathrm{d}(\pi_v)$ of the chosen uniformizer spans $\Omega_{F/K}$ over $F$. Let $w$ be a $K$-algebra automorphism of $F$, and let $\omega \in \Omega_{F/K}$ be regular, meaning that for every place $v$ there is $f$ in the valuation subring of $v$ with $\omega = f \cdot \mathrm{d}C_v$. Then the image of $\omega$ under [`AlgebraicCurve.Differential.pullbackAlong`](def/AlgebraicCurve_DifferentialPushPull.html#L16) applied to the $K$-algebra homomorphism underlying $w$ — the $K$-linear base-change map $\Omega_{F/K} \to \Omega_{F/K}$ induced by viewing $F$ as an $F$-algebra via $w$ — is again regular in the same sense.
--
--   This is the statement that a $K$-automorphism of a one-variable function field carries differentials of the first kind to differentials of the first kind, in the formulation where regularity at a place is tested against the differential of that place's chosen uniformizer. It is used in the construction of the Hecke action on regular differentials of a modular curve, being cited in the treatment of $m$-torsion differentials attached to Hecke torsion classes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_pullbackAlong_mem_regularDifferentials_of_mem_of_isCurveOver.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_AlgebraicCurve_DifferentialPushPull
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve in

theorem AlgebraicCurve.pullbackAlong_mem_regularDifferentials_of_mem_of_isCurveOver
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    [PerfectField K] [Algebra.EssFiniteType K F] [AlgebraicCurve.IsCurveOver K F]
    [∀ v : AlgebraicCurve.Place K F, v.DCoordGenerates]
    (w : F ≃ₐ[K] F) {ω : Ω[F⁄K]} (hω : ω ∈ AlgebraicCurve.regularDifferentials K F) :
    AlgebraicCurve.Differential.pullbackAlong (w : F →ₐ[K] F) ω ∈ AlgebraicCurve.regularDifferentials K F := by sorry

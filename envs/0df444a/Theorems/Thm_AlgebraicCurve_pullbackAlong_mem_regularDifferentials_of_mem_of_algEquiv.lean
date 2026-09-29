-- Prove2me | Theorems.Thm_AlgebraicCurve_pullbackAlong_mem_regularDifferentials_of_mem_of_algEquiv
-- name    : AlgebraicCurve.pullbackAlong_mem_regularDifferentials_of_mem_of_algEquiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/c946fec8-8d96-5eb9-b275-913571e3c92c
-- title:
--   Regular differentials are preserved by a K-isomorphism of function fields
-- statement:
--   Let $K$ be a perfect field and let $F, F'$ be field extensions of $K$, with $F'$ essentially of finite type over $K$ and satisfying `IsCurveOver K F'`: every nonzero $f \in F'$ is the divisor of a degree-zero divisor (for each place $v$ the coefficient is $v.\mathrm{ord}\, f$), each place of $F'/K$ has residue field finite over $K$, and $\Omega_{F'/K}$ is free of rank one over $F'$. Here a place of a field extension $L/K$ is a valuation subring of $L$ containing the image of $K$, distinct from $L$ itself, and a principal ideal ring. Assume further that for every place $v$ of $F/K$ and every place $w$ of $F'/K$ the predicate `DCoordGenerates` holds, i.e. the differential $d$ of the chosen uniformiser spans $\Omega$ over the ambient field. Let $\Phi : F \simeq_K F'$ be a $K$-algebra isomorphism and let $\eta \in \Omega_{F/K}$ be regular, meaning that for every place $v$ of $F/K$ there is $f$ in the valuation ring of $v$ with $\eta = f \cdot v.\mathrm{dCoord}$. Then the image of $\eta$ under `Differential.pullbackAlong` applied to $\Phi$ viewed as a $K$-algebra homomorphism — the $K$-linear map $\Omega_{F/K} \to \Omega_{F'/K}$ induced by the $F$-algebra structure on $F'$ along $\Phi$ — is again regular, i.e. lies in `regularDifferentials K F'`.
--
--   This is the transport of the module of regular (holomorphic) differentials of a curve along an isomorphism of its function field over the base, stated for the place-theoretic definition of regularity used throughout the divisor-theoretic development. It is used in the modular-curve chapter, where differentials on a modular curve are compared with differentials in a chart through a $K$-algebra isomorphism of function fields, by [`ModularCurve.res_mem_regularDifferentialsBar_of_chartMap_of_neZero`](thm.html#ModularCurve.res_mem_regularDifferentialsBar_of_chartMap_of_neZero) and [`ModularCurve.mem_span_range_res_of_mem_regularDifferentialsBar_of_chartMap_of_neZero`](thm.html#ModularCurve.mem_span_range_res_of_mem_regularDifferentialsBar_of_chartMap_of_neZero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_pullbackAlong_mem_regularDifferentials_of_mem_of_algEquiv.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_AlgebraicCurve_DifferentialPushPull
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.pullbackAlong_mem_regularDifferentials_of_mem_of_algEquiv
    {K : Type*} [Field K] [PerfectField K] {F F' : Type*} [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [Algebra.EssFiniteType K F'] [IsCurveOver K F']
    [∀ v : Place K F, v.DCoordGenerates] [∀ w : Place K F', w.DCoordGenerates]
    (Φ : F ≃ₐ[K] F') (η : Ω[F⁄K]) (hη : η ∈ regularDifferentials K F) :
    Differential.pullbackAlong (Φ : F →ₐ[K] F') η ∈ regularDifferentials K F' := by sorry

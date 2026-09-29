-- Prove2me | Theorems.Thm_AlgebraicCurve_inv_smul_D_eq_zero_iff_exists_pow_eq
-- name    : AlgebraicCurve.inv_smul_D_eq_zero_iff_exists_pow_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/b9b91091-fbad-5a24-8904-0a5defc4144b
-- title:
--   Logarithmic derivative vanishes iff p-th power
-- statement:
--   Let $K$ be a perfect field of characteristic $p$, $p$ a prime, and let $F$ be a field equipped with a $K$-algebra structure which is essentially of finite type over $K$ and satisfies `IsCurveOver K F`, i.e. $F/K$ has principal divisors (every nonzero $h\in F$ admits a divisor $D$ on the places of $F/K$ with $D(v)=\operatorname{ord}_v(h)$ for every place $v$ and $\deg D=0$), every place of $F/K$ has residue field finite-dimensional over $K$, and the module of Kähler differentials $\Omega_{F/K}$ is free of rank $1$ over $F$; here a place is a proper valuation subring of $F$ containing the image of $K$ whose ideals are all principal. Let $f\in F$ with $f\neq 0$. The theorem asserts the equivalence of the vanishing of the logarithmic differential $f^{-1}\cdot \mathrm{d}f=0$ in $\Omega_{F/K}$, where $\mathrm{d}$ is the universal derivation `KaehlerDifferential.D K F`, with the existence of $g\in F$ such that $g^{p}=f$. No separate nonvanishing condition on $g$ is imposed in the conclusion.
--
--   This identifies the kernel of the logarithmic derivative on $F^{\times}$ for a one-variable function field over a perfect field of characteristic $p$ as the subgroup of $p$-th powers. It is used in the treatment of the modular curve, where it feeds the criteria [`ModularCurve.exists_eq_mul_pow_mul_of_coe_eq_coeffMap_of_forall_dvd_ord`](thm.html#ModularCurve.exists_eq_mul_pow_mul_of_coe_eq_coeffMap_of_forall_dvd_ord) and [`ModularCurve.inv_smul_D_eq_zero_iff_mk_eq_zero_of_coe_eq_coeffMap_of_forall_mul_eq_ord`](thm.html#ModularCurve.inv_smul_D_eq_zero_iff_mk_eq_zero_of_coe_eq_coeffMap_of_forall_mul_eq_ord).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_inv_smul_D_eq_zero_iff_exists_pow_eq.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_AlgebraicCurve_LogDeRhamH1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.inv_smul_D_eq_zero_iff_exists_pow_eq
    {K : Type*} [Field K] [PerfectField K] {F : Type*} [Field F] [Algebra K F]
    [Algebra.EssFiniteType K F] [IsCurveOver K F]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (f : F) (hf : f ≠ 0) :
    f⁻¹ • KaehlerDifferential.D K F f = 0 ↔ ∃ g : F, g ^ p = f := by sorry

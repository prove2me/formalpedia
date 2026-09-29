-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_hasSimplePoleAt_inv_smul_D_and_hasSimpleResidue_intCast_ord
-- name    : AlgebraicCurve.Place.hasSimplePoleAt_inv_smul_D_and_hasSimpleResidue_intCast_ord
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/5f5a4ec5-d1ba-5972-b17b-129d0aae6b60
-- title:
--   Simple pole and residue ordᵥ(f) of df/f
-- statement:
--   Let $K$ be an algebraically closed field and $F$ a field equipped with a $K$-algebra structure which is of essentially finite type over $K$ and satisfies `IsCurveOver K F`, i.e. every nonzero $f \in F$ admits a divisor of degree $0$ whose value at each place is $\operatorname{ord}_v(f)$, each place of $F/K$ has residue field finite over $K$, and the module of Kähler differentials $\Omega[F\!\setminus\!K]$ is free of rank one over $F$. Let $f \in F$ be nonzero and let $v$ be a place of $F$ over $K$, that is, a valuation subring of $F$ containing $\operatorname{im}(K \to F)$, different from $F$ itself and a principal ideal ring. Write $\pi$ for the chosen irreducible element `v.uniformizer` of that valuation ring, $\mathrm{d}_v = D_{K/F}\pi$ for the associated coordinate differential `v.dCoord`, and $\operatorname{ord}_v(f) = -\log$ of the value of $f$ under the adic valuation attached to $v$. Then the logarithmic differential $f^{-1} \cdot D_{K/F} f$ has a simple pole at $v$ and simple residue the image of the integer $\operatorname{ord}_v(f)$ in $K$: there is $g \in F$ with $\pi g$ in the valuation ring and $f^{-1} \cdot D_{K/F} f = g \cdot \mathrm{d}_v$, and there is $g \in F$ with $f^{-1} \cdot D_{K/F} f = g \cdot \mathrm{d}_v$ such that $\pi g$ lies in the valuation ring and its residue equals the image of $(\operatorname{ord}_v(f) : K)$ in the residue field of $v$.
--
--   This is the residue theorem's local input: on a curve the logarithmic differential $df/f$ has at worst a simple pole at every place, with residue the order of vanishing of $f$ there. It is used in the construction of the Abel–Jacobi and $\mathrm{dlog}$ maps on divisors of modular curves, and in the comparison of divisor-class data with differentials.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_hasSimplePoleAt_inv_smul_D_and_hasSimpleResidue_intCast_ord.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_AlgebraicCurve_PolarDifferentials

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.Place.hasSimplePoleAt_inv_smul_D_and_hasSimpleResidue_intCast_ord
    {K : Type*} [Field K] [IsAlgClosed K] {F : Type*} [Field F] [Algebra K F]
    [Algebra.EssFiniteType K F] [IsCurveOver K F]
    (f : F) (hf : f ≠ 0) (v : Place K F) :
    v.HasSimplePoleAt (f⁻¹ • KaehlerDifferential.D K F f) ∧
      v.HasSimpleResidue (f⁻¹ • KaehlerDifferential.D K F f) ((v.ord f : ℤ) : K) := by sorry

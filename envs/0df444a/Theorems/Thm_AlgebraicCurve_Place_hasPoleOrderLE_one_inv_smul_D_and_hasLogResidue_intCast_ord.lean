-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_hasPoleOrderLE_one_inv_smul_D_and_hasLogResidue_intCast_ord
-- name    : AlgebraicCurve.Place.hasPoleOrderLE_one_inv_smul_D_and_hasLogResidue_intCast_ord
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/f55c314e-8dd7-57e6-a4d7-c03570b30b0f
-- title:
--   Logarithmic differential: simple poles with residue ordᵥ f
-- statement:
--   Let $K$ be an algebraically closed field and $F$ a field equipped with a $K$-algebra structure which is essentially of finite type over $K$ and satisfies `IsCurveOver K F`, i.e. every nonzero $f \in F$ admits a divisor of degree $0$ whose value at each place is $\operatorname{ord}_v f$, each place of $F/K$ has residue field finite over $K$, and $\Omega[F/K]$ is a free $F$-module of rank one. Let $f \in F$ with $f \neq 0$, and let $v$ be a place of $F/K$, that is, a valuation subring of $F$ containing the image of $K$, distinct from $F$ itself and a principal ideal ring. The conclusion is a conjunction about the logarithmic differential $f^{-1} \cdot d f = f^{-1} \cdot \mathrm{D}_{K/F}(f)$, the dot denoting the scalar action. First, `HasPoleOrderLE 1`: there is $h \in F$ with $\pi h$ in the valuation subring of $v$ and $f^{-1}\,df = h \cdot \omega_v$, where $\pi$ is the chosen uniformizer of $v$ and $\omega_v = \mathrm{D}_{K/F}(\pi)$ is the associated coordinate differential. Second, `HasLogResidue` with value $(\operatorname{ord}_v f : K)$, the image in $K$ of the integer $\operatorname{ord}_v f = -\log$ of the adic valuation of $f$: there is $h \in F$ with $f^{-1}\,df = h \cdot \omega_v$ such that $\pi h$ lies in the valuation subring and its image in the residue field of $v$ equals the image of $(\operatorname{ord}_v f : K)$ under the structure map $K \to \kappa(v)$.
--
--   This is the standard local statement that $d f / f$ has at worst a simple pole at every place, with residue the order of vanishing of $f$ there; it is the starting point for the theory of logarithmic differentials on a curve and underlies the residue computations used in the logarithmic de Rham cohomology of $F/K$. It is cited by [`AlgebraicCurve.Place.hasSimplePoleAt_inv_smul_D_and_hasSimpleResidue_intCast_ord`](thm.html#AlgebraicCurve.Place.hasSimplePoleAt_inv_smul_D_and_hasSimpleResidue_intCast_ord).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_hasPoleOrderLE_one_inv_smul_D_and_hasLogResidue_intCast_ord.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_AlgebraicCurve_LogDeRhamH1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.Place.hasPoleOrderLE_one_inv_smul_D_and_hasLogResidue_intCast_ord
    {K : Type*} [Field K] [IsAlgClosed K] {F : Type*} [Field F] [Algebra K F]
    [Algebra.EssFiniteType K F] [IsCurveOver K F]
    (f : F) (hf : f ≠ 0) (v : Place K F) :
    v.HasPoleOrderLE 1 (f⁻¹ • KaehlerDifferential.D K F f) ∧
      v.HasLogResidue (f⁻¹ • KaehlerDifferential.D K F f) ((v.ord f : ℤ) : K) := by sorry

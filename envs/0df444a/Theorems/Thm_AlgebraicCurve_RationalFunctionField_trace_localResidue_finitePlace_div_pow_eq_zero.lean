-- Prove2me | Theorems.Thm_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero
-- name    : AlgebraicCurve.RationalFunctionField.trace_localResidue_finitePlace_div_pow_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/d1cce741-7d10-5660-83bd-b2b7f0f197ec
-- title:
--   Traceless residues of higher poles at finite places of K(X)
-- statement:
--   Let $K$ be a perfect field, and assume that $K(X)$ is a curve over $K$ in the sense of the project's `IsCurveOver` class (principal divisors of degree zero exist for every nonzero function, every place has residue field finite over $K$, and $\Omega[K(X)/K]$ is free of rank one over $K(X)$), that $\Omega[K(X)/K]$ is nontrivial, and that every place $v$ of $K(X)$ satisfies `DCoordGenerates`, i.e. the differential $d(\pi_v)$ of a uniformiser of $v$ spans $\Omega[K(X)/K]$ over $K(X)$. Let $p \in K[X]$ be monic and irreducible, let $c \in K[X]$ have $\deg c < \deg p$, and let $m \ge 2$. Write $v$ for the finite place `finitePlace K hp` attached to $p$, namely the place given by the valuation subring of the valuation on $K(X)$ associated with the height-one prime $(p)$ of $K[X]$, and let $\kappa(v)$ be its residue field. Let $a \in K(X)$ be the `differentialCoeff` of $v$ at $d X$, that is the unique coefficient with $dX = a \cdot d(\pi_v)$. Then the canonical local residue `localResidue` of $v$, a $K$-linear map $K(X) \to \kappa(v)$, sends $(c/p^m)\,a$ to an element of trace zero: $\operatorname{Tr}_{\kappa(v)/K}\bigl(\operatorname{res}_v((c/p^{m})\,a)\bigr) = 0$.
--
--   This is the higher-pole case of the residue theorem on the projective line over a perfect field, at a finite place of arbitrary degree: the residue itself need not vanish when $\deg p \ge 2$, but its trace down to $K$ does. It is used in the proof of the residue theorem for $K(X)$ over a perfect field, [`AlgebraicCurve.residueTheorem_ratFunc_of_perfectField`](thm.html#AlgebraicCurve.residueTheorem_ratFunc_of_perfectField).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_CanonicalDivisor
import Definitions.Def_ModularCurve_CanonicalDivisorUniformizer
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_LocalResidue
import Definitions.Def_AlgebraicCurve_WeilOfKaehler
import Definitions.Def_AlgebraicCurve_TateResidueCurrency
import Definitions.Def_AlgebraicCurve_CanonicalLocalResidueInstanceV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial

theorem AlgebraicCurve.RationalFunctionField.trace_localResidue_finitePlace_div_pow_eq_zero
    (K : Type*) [Field K] [PerfectField K] [DecidableEq (RatFunc K)]
    [AlgebraicCurve.IsCurveOver K (RatFunc K)]
    [∀ v : AlgebraicCurve.Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
    {p c : K[X]} (hmon : p.Monic) (hp : Irreducible p) (hc : c.degree < p.degree) {m : ℕ} (hm : 2 ≤ m) :
    Algebra.trace K (AlgebraicCurve.RationalFunctionField.finitePlace K hp).ResidueField
        ((AlgebraicCurve.RationalFunctionField.finitePlace K hp).localResidue
          (algebraMap K[X] (RatFunc K) c / algebraMap K[X] (RatFunc K) p ^ m
            * (AlgebraicCurve.RationalFunctionField.finitePlace K hp).differentialCoeff
                (KaehlerDifferential.D K (RatFunc K) (RatFunc.X : RatFunc K)))) = 0 := by sorry

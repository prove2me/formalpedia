-- Prove2me | Theorems.Thm_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_add_trace_localResidue_placeInfty_eq_zero
-- name    : AlgebraicCurve.RationalFunctionField.trace_localResidue_finitePlace_add_trace_localResidue_placeInfty_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/e09bdf27-26fb-5b56-85c8-a682c60b73a5
-- title:
--   Simple-pole residue cancellation for c dX/p on P¹
-- statement:
--   Let $K$ be a perfect field and $\mathrm{RatFunc}\,K = K(X)$ its rational function field, subject to three structural assumptions on the pair $K \subseteq K(X)$: a choice, for every place $v$ of $K(X)$ over $K$ (a valuation subring of $K(X)$ containing $K$, proper, and a principal ideal ring), of canonical local residue data, consisting of a $K$-linear residue map $\mathrm{res}_v \colon K(X) \to \kappa(v)$ into the residue field of $v$ satisfying the local residue axioms together with the vanishing $\mathrm{res}_v\big((\pi_v^{\,n+1})^{-1}\big) = 0$ for all $n \ge 1$, where $\pi_v$ is the chosen uniformiser; the requirement that for every $v$ the element $\mathrm{d}\pi_v \in \Omega_{K(X)/K}$ spans $\Omega_{K(X)/K}$ as a $K(X)$-module; and nontriviality of $\Omega_{K(X)/K}$. Let $p \in K[X]$ be monic and irreducible and let $c \in K[X]$ have $\deg c < \deg p$. Write $v_p$ for the place attached to the height-one prime $(p)$ of $K[X]$, i.e. the valuation subring of the $(p)$-adic valuation of $K(X)$, and $v_\infty$ for the place given by the valuation subring of the valuation at infinity. For a place $v$ and $\omega \in \Omega_{K(X)/K}$ let $\mathrm{differentialCoeff}_v(\omega)$ be the coefficient $f \in K(X)$ with $\omega = f \cdot \mathrm{d}\pi_v$ (and $0$ if no such $f$ exists). Then $$\mathrm{Tr}_{\kappa(v_p)/K}\Big(\mathrm{res}_{v_p}\big(\tfrac{c}{p}\,\mathrm{differentialCoeff}_{v_p}(\mathrm{d}X)\big)\Big) + \mathrm{Tr}_{\kappa(v_\infty)/K}\Big(\mathrm{res}_{v_\infty}\big(\tfrac{c}{p}\,\mathrm{differentialCoeff}_{v_\infty}(\mathrm{d}X)\big)\Big) = 0,$$ the quotient $c/p$ being formed from the images of $c$ and $p$ in $K(X)$ and $\mathrm{d}X$ denoting the universal derivation of $K(X)$ over $K$ applied to $X$.
--
--   This is the simple-pole case of the residue theorem on the projective line over a perfect field: the only poles of $\frac{c}{p}\,dX$ with $\deg c < \deg p$ are the place $(p)$ and the place at infinity, and the two traced residues are negatives of one another, each being (up to sign) the coefficient of $X^{\deg p - 1}$ in $c$ by Euler's interpolation identity. It is used in the proof of the general residue theorem for the rational function field, [`AlgebraicCurve.residueTheorem_ratFunc_of_perfectField`](thm.html#AlgebraicCurve.residueTheorem_ratFunc_of_perfectField).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_add_trace_localResidue_placeInfty_eq_zero.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Definitions.Def_ModularCurve_CanonicalDivisor
import Definitions.Def_ModularCurve_CanonicalDivisorUniformizer
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_LocalResidue

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial

theorem AlgebraicCurve.RationalFunctionField.trace_localResidue_finitePlace_add_trace_localResidue_placeInfty_eq_zero
    (K : Type*) [Field K] [PerfectField K] [DecidableEq (RatFunc K)]
    [AlgebraicCurve.HasCanonicalLocalResidueKStar K (RatFunc K)]
    [∀ v : AlgebraicCurve.Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
    {p c : K[X]} (hmon : p.Monic) (hp : Irreducible p) (hc : c.degree < p.degree) :
    Algebra.trace K (AlgebraicCurve.RationalFunctionField.finitePlace K hp).ResidueField
        ((AlgebraicCurve.RationalFunctionField.finitePlace K hp).localResidue
          (algebraMap K[X] (RatFunc K) c / algebraMap K[X] (RatFunc K) p
            * (AlgebraicCurve.RationalFunctionField.finitePlace K hp).differentialCoeff
                (KaehlerDifferential.D K (RatFunc K) (RatFunc.X : RatFunc K))))
      + Algebra.trace K (AlgebraicCurve.RationalFunctionField.placeInfty K).ResidueField
        ((AlgebraicCurve.RationalFunctionField.placeInfty K).localResidue
          (algebraMap K[X] (RatFunc K) c / algebraMap K[X] (RatFunc K) p
            * (AlgebraicCurve.RationalFunctionField.placeInfty K).differentialCoeff
                (KaehlerDifferential.D K (RatFunc K) (RatFunc.X : RatFunc K)))) = 0 := by sorry

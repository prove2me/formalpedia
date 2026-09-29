-- Prove2me | Theorems.Thm_AlgebraicCurve_riemannGenusReached_of_stichtenothGenusExists
-- name    : AlgebraicCurve.riemannGenusReached_of_stichtenothGenusExists
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/e595fa42-1674-5f5e-84df-d2029ea09cf9
-- title:
--   Attained Riemann genus equals the canonical genus
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, subject to the following structural assumptions: `IsCurveOver K F`, i.e. principal divisors are available, every place $v$ of $F/K$ has residue field finite over $K$, and $\Omega[F/K]$ is free of rank one over $F$; `HasCanonicalDivisor`, i.e. for every nonzero $\omega \in \Omega[F/K]$ there is a divisor whose value at each place $v$ is $v.\mathrm{ordDifferential}\,\omega$, the divisor so chosen being written $\mathrm{canonicalDivisorOf}$; at every place $v$ the single element $v.\mathrm{dCoord}$ spans $\Omega[F/K]$ over $F$; and `HasCanonicalLocalResidueKStar`, a choice of canonical local residue data at each place. Assume further: (`hSG`) the Stichtenoth genus exists, i.e. there is at least one place, $L(0)$ is finite-dimensional over $K$, and for some $\gamma \in \mathbb{Z}$ some divisor $D_0$ has $L(D_0)$ finite-dimensional, $\deg D_0 - \ell(D_0) = \gamma - 1$ and $\deg D - \ell(D) \le \gamma - 1$ for every divisor $D$; (`hWK`) Weil and Kähler differentials agree, i.e. for every nonzero $\omega$ the associated Weil differential $\mathrm{weilOfKaehler}$ is nonzero, lies in $\omega\text{-space}$ of $\mathrm{canonicalDivisorOf}\,\omega$ (the annihilator of the bounded-principal adèle subspace), and $\mathrm{canonicalDivisorOf}\,\omega$ dominates every divisor $D$ with $\mathrm{weilOfKaehler}\in\omega\text{-space}(D)$; (`hC`) $L(0)$ is exactly the image of $K$ in $F$. Then the same maximum is attained with the specific value $\gamma = \mathrm{genus}\,K\,F$, defined as $\lfloor(\deg W + 2)^{+}/2\rfloor$ for $W$ the canonical divisor of a chosen nonzero differential (and $0$ if $\Omega[F/K]=0$): there is a place, $L(0)$ is finite-dimensional, and some divisor $D_0$ has $L(D_0)$ finite-dimensional, $\deg D_0 - \ell(D_0) = \mathrm{genus}\,K\,F - 1$, and $\deg D - \ell(D) \le \mathrm{genus}\,K\,F - 1$ for all $D$.
--
--   This identifies the abstract genus arising from Riemann's inequality (the maximum of $\deg D - \ell(D)$, increased by one) with the genus read off from the degree of a canonical divisor, under the hypothesis that Weil differentials and Kähler differentials determine the same canonical class and that the constants of $F$ are just $K$. It supplies the hypothesis needed to run the Riemann–Roch index formula with the canonical genus, and is used in the analysis of differentials on modular curves for the Hecke-module arguments.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_riemannGenusReached_of_stichtenothGenusExists.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_PoleDivisorPackage
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Definitions.Def_ModularCurve_CanonicalDivisor
import Definitions.Def_ModularCurve_CanonicalDivisorUniformizer
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_LocalResidue
import Definitions.Def_AlgebraicCurve_WeilOfKaehler
import Definitions.Def_AlgebraicCurve_RiemannRochRows

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicCurve

theorem riemannGenusReached_of_stichtenothGenusExists {K : Type*} {F : Type*} [Field K] [Field F] [Algebra K F]
    [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)]
    [∀ v : Place K F, v.DCoordGenerates] [HasCanonicalLocalResidueKStar K F]
    (hSG : StichtenothGenusExists K F)
    (hWK : WeilKaehlerAgree K F) (hC : ConstantsAreBase K F) :
    RiemannGenusReached K F (genus K F) := by sorry

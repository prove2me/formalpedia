-- Prove2me | Theorems.Thm_AlgebraicCurve_omegaSpace_eq_bot_of_degree_canonicalDivisorOf_lt
-- name    : AlgebraicCurve.omegaSpace_eq_bot_of_degree_canonicalDivisorOf_lt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/c287b268-4551-5818-8d42-e1b19e528a19
-- title:
--   Vanishing of Ω(D) when deg D>deg(ω)
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra satisfying `IsCurveOver K F`, i.e. every non-zero $f \in F$ has a divisor recording its orders $v.\mathrm{ord}\,f$ at all places and of degree $0$, each residue field $v.\mathrm{ResidueField}$ is finite over $K$, and $\Omega[F/K]$ is free of rank one over $F$; assume further that $\mathrm{Place}\,K\,F$ is non-empty, that $\mathrm{LSpace}\,0$ (the Riemann–Roch space of the zero divisor) is finite-dimensional over $K$, that `HasCanonicalDivisor` holds, so that every non-zero $\omega \in \Omega[F/K]$ has a divisor $\mathrm{canonicalDivisorOf}$ whose value at each place $v$ is $v.\mathrm{ordDifferential}\,\omega$, that at every place the element $v.\mathrm{dCoord}$ spans $\Omega[F/K]$ over $F$, and that canonical local residue data are given at every place. Suppose $\gamma \in \mathbb{Z}$ and a divisor $D_0$ satisfy $\mathrm{RiemannGenusReachedAt}\,\gamma\,D_0$: $\mathrm{LSpace}\,D_0$ is finite-dimensional, $\deg D_0 - \ell(D_0) = \gamma - 1$, and $\deg D - \ell(D) \le \gamma - 1$ for every divisor $D$. Suppose $\mathrm{WeilKaehlerAgree}\,K\,F$: for every non-zero Kähler differential, the associated Weil differential $\mathrm{weilOfKaehler}$ is non-zero, lies in $\mathrm{omegaSpace}$ of its canonical divisor, and lies in $\mathrm{omegaSpace}\,D$ only for divisors $D \le \mathrm{canonicalDivisorOf}$. Then for a non-zero $\omega$, a divisor $D$ with $\mathrm{omegaSpace}\,D$ finite-dimensional over $K$, and $\deg(\mathrm{canonicalDivisorOf}\ \omega) < \deg D$, the space $\mathrm{omegaSpace}\,D$ — the annihilator, inside the $K$-dual of the adele space, of the image of $\mathrm{adeleBdd}\,D$ together with the principal adeles — is the zero submodule.
--
--   This is the standard vanishing statement of the Riemann–Roch theory of Weil differentials: the space $\Omega(D)$ of Weil differentials bounded by $D$ vanishes as soon as $\deg D$ exceeds the degree of a canonical divisor. It is used in the modular-curve setting to force the vanishing of the corresponding differential space at the edge of the weight range, via [`ModularCurve.omegaSpace_eq_bot_of_two_mul_eq_add_one`](thm.html#ModularCurve.omegaSpace_eq_bot_of_two_mul_eq_add_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_omegaSpace_eq_bot_of_degree_canonicalDivisorOf_lt.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_WeilOfKaehler

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.omegaSpace_eq_bot_of_degree_canonicalDivisorOf_lt
    {K F : Type*} [Field K] [Field F] [Algebra K F] [AlgebraicCurve.IsCurveOver K F] [Nonempty (AlgebraicCurve.Place K F)]
    [FiniteDimensional K ↥(AlgebraicCurve.LSpace (0 : AlgebraicCurve.Divisor K F))]
    [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := F)]
    [∀ v : AlgebraicCurve.Place K F, v.DCoordGenerates] [AlgebraicCurve.HasCanonicalLocalResidueKStar K F]
    {γ : ℤ} {D₀ : AlgebraicCurve.Divisor K F} (h : AlgebraicCurve.RiemannGenusReachedAt γ D₀)
    (hWK : AlgebraicCurve.WeilKaehlerAgree K F) {ω : Ω[F⁄K]} (hω : ω ≠ 0) (D : AlgebraicCurve.Divisor K F)
    [FiniteDimensional K ↥(AlgebraicCurve.omegaSpace (K := K) (F := F) D)]
    (hdeg : AlgebraicCurve.Divisor.degree (AlgebraicCurve.canonicalDivisorOf hω) < AlgebraicCurve.Divisor.degree D) :
    AlgebraicCurve.omegaSpace (K := K) (F := F) D = ⊥ := by sorry

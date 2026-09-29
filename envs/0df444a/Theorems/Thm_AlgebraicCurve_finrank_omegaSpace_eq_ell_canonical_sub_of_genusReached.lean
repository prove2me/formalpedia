-- Prove2me | Theorems.Thm_AlgebraicCurve_finrank_omegaSpace_eq_ell_canonical_sub_of_genusReached
-- name    : AlgebraicCurve.finrank_omegaSpace_eq_ell_canonical_sub_of_genusReached
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/cec32167-97af-556c-956a-5531edbb7d86
-- title:
--   dim_K Ω_F(D) = ℓ((ω) - D)
-- statement:
--   Let $F$ be a field extension of a field $K$ which is a curve over $K$ in the sense of `IsCurveOver`, so that principal divisors are available, every place of $F/K$ has residue field finite over $K$, and $\Omega[F/K]$ is free of rank one over $F$; assume further that $F/K$ has at least one place, that the Riemann–Roch space $L(0)$ is finite-dimensional over $K$, that every nonzero Kähler differential $\omega$ admits a divisor whose coefficient at each place $v$ is $v.\mathrm{ordDifferential}\,\omega$ (`HasCanonicalDivisor`, from which `canonicalDivisorOf` selects such a divisor), that at each place $v$ the element $v.\mathrm{dCoord}$ spans $\Omega[F/K]$ over $F$, and that a canonical local residue datum is chosen at every place. Let $\gamma \in \mathbb{Z}$ and let $D_0$ be a divisor at which the Riemann genus is reached: $L(D_0)$ is finite-dimensional, $\deg D_0 - \ell(D_0) = \gamma - 1$, and $\deg D - \ell(D) \le \gamma - 1$ for every divisor $D$. Assume the Weil–Kähler agreement `WeilKaehlerAgree K F`: for every nonzero $\omega$ the associated Weil differential `weilOfKaehler K F hω` is nonzero, lies in `omegaSpace (canonicalDivisorOf hω)`, and lies in `omegaSpace D` only for divisors $D \le$ `canonicalDivisorOf hω`. Then for every nonzero $\omega \in \Omega[F/K]$ and every divisor $D$, the $K$-dimension of `omegaSpace D` — the annihilator in the $K$-dual of the adele space of the submodule spanned by the adeles bounded by $D$ together with the global (principal) adeles — equals $\ell(\,(\omega) - D\,)$, the $K$-dimension of the Riemann–Roch space of `canonicalDivisorOf hω` $- D$.
--
--   This is the dimension form of Weil/Serre duality for function fields: the space of Weil differentials bounded by $D$ has the same $K$-dimension as the Riemann–Roch space of the canonical divisor minus $D$ (Stichtenoth I.5.14). It is used, for instance, to show that `omegaSpace D` vanishes once $\deg D$ exceeds the degree of the canonical divisor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_finrank_omegaSpace_eq_ell_canonical_sub_of_genusReached.lean

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

theorem finrank_omegaSpace_eq_ell_canonical_sub_of_genusReached {K : Type*} {F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F] [Nonempty (Place K F)] [FiniteDimensional K (LSpace (0 : Divisor K F))] [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates] [HasCanonicalLocalResidueKStar K F]
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀)
    (hWK : WeilKaehlerAgree K F) {ω : Ω[F⁄K]} (hω : ω ≠ 0) (D : Divisor K F) :
    Module.finrank K (omegaSpace (K := K) (F := F) D) = ell (canonicalDivisorOf hω - D) := by sorry

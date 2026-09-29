-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_linearEquiv_regularDifferentials_omegaSpace_zero
-- name    : AlgebraicCurve.exists_linearEquiv_regularDifferentials_omegaSpace_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/ed84f54e-6387-5720-8dc8-b4a52d8bdce4
-- title:
--   Regular differentials versus Weil differentials of divisor 0
-- statement:
--   Let $K$ be a perfect field and $F$ a field extension of $K$ which is essentially of finite type over $K$ and satisfies `IsCurveOver K F`: principal divisors are available, each place $v$ of $F/K$ has residue field finite over $K$, and $\Omega_{F/K}$ is free of rank one over $F$. Assume moreover `HasCanonicalDivisor`, i.e. every nonzero $\omega \in \Omega_{F/K}$ admits a divisor whose coefficient at each place $v$ is $\mathrm{ord}_v(\omega)$; that at every place the element $d\pi_v$ spans $\Omega_{F/K}$ over $F$ (`DCoordGenerates`); and that a canonical local residue datum over $K$ is chosen at every place (`HasCanonicalLocalResidueKStar`). Assume further $hC$: the Riemann–Roch space $L(0)$ equals the image of $K$ in $F$, and $hRT$: the residue theorem, namely for every nonzero $\omega$ and every $f \in F$ the functional $\lambda_\omega =$ `weilOfKaehler` vanishes on the diagonal adele of $f$. The conclusion is the existence of a $K$-linear isomorphism $e$ from the module of regular differentials — those $\omega$ such that at every place $v$ one has $\omega = f\,d\pi_v$ for some $f$ in the valuation ring of $v$ — onto $\Omega_F(0)$, the annihilator inside $\mathrm{Hom}_K(\mathbb{A}_F, K)$ of the sum of the adeles bounded by the divisor $0$ and of the diagonal copy of $F$, such that for every regular $\omega$ whose underlying differential is nonzero, $e(\omega)$ is the functional $\alpha \mapsto \sum_v \mathrm{kaehlerResidueTerm}\,\omega\,\alpha\,v$ given by `weilOfKaehler K F hω`.
--
--   This is the comparison between Kähler differentials regular everywhere and Weil differentials bounded by the zero divisor, over a perfect but not necessarily algebraically closed base; classically it underlies the identification $H^0(X,\Omega^1_X) \cong H^1(X,\mathcal{O}_X)^\vee$. It is used in the proof that the Serre pairing and its flip are bijective.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_linearEquiv_regularDifferentials_omegaSpace_zero.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_LocalResidue
import Definitions.Def_AlgebraicCurve_WeilOfKaehler
import Definitions.Def_AlgebraicCurve_RegularDifferentials

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open KaehlerDifferential
namespace AlgebraicCurve

theorem exists_linearEquiv_regularDifferentials_omegaSpace_zero {K : Type*} {F : Type*} [Field K] [Field F] [Algebra K F]
    [PerfectField K] [Algebra.EssFiniteType K F] [IsCurveOver K F]
    [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates]
    [HasCanonicalLocalResidueKStar K F]
    (hC : ConstantsAreBase K F) (hRT : ResidueTheorem K F) :
    ∃ e : ↥(regularDifferentials K F) ≃ₗ[K] ↥(omegaSpace (K := K) (F := F) (0 : Divisor K F)),
      ∀ (ω : ↥(regularDifferentials K F)) (hω : (ω : Ω[F⁄K]) ≠ 0),
        ((e ω : ↥(omegaSpace (K := K) (F := F) (0 : Divisor K F))) : Module.Dual K ↥(adeleSpace K F))
          = weilOfKaehler K F hω := by sorry

-- Prove2me | Theorems.Thm_AlgebraicCurve_serrePairing_pullbackAlong_eq_serrePairing_traceAlong
-- name    : AlgebraicCurve.serrePairing_pullbackAlong_eq_serrePairing_traceAlong
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/4dfc93fe-aa7e-5381-901b-34d3ce888c61
-- title:
--   Serre pairing is adjoint for pull-back and trace along φ
-- statement:
--   Let $K$, $F$, $F'$ be fields with $F$, $F'$ algebras over $K$, both equipped with a chosen canonical local residue datum at every place (a local residue map annihilating $(\pi_v^{n+1})^{-1}$ for $n\ge 1$), with the property that at each place the differential $\mathrm{d}\pi_v$ of a uniformiser spans the module of Kähler differentials over the field, with $\Omega[F\!\restriction\!K]$ and $\Omega[F'\!\restriction\!K]$ nontrivial, and with the two finiteness/degree clauses `HasCanonicalDivisor` (for each nonzero differential the orders of its differential coefficient form a divisor) and `HasPrincipalDivisors` (each nonzero function has a divisor, of degree zero). Assume the residue theorems `hRT`, `hRT'`: for each nonzero differential the total residue sum of a diagonal adele vanishes. Let $\varphi\colon F\to F'$ be an integral $K$-algebra homomorphism such that `TraceIntegralAlong` holds, i.e. whenever $f'\in F'$ is integral at every place above $v$ then $\mathrm{Tr}_{F'/F}(f')$ is integral at $v$, and such that `FibreResidueIdentityAlong` holds, i.e. for all $v$, $\omega\in\Omega[F\!\restriction\!K]$ and $f'\in F'$ the sum over the fibre of $v$ of the residue terms of $\varphi^*\omega$ against the constant adele $f'$ equals the residue term of $\omega$ at $v$ against the constant adele $\mathrm{Tr}_{F'/F}(f')$. Let $S_0\cup S_1$ be all places of $F$, let $\omega$ be a regular differential on $F$ (at each place $f\cdot \mathrm{d}\pi_v$ with $f$ integral) whose pull-back $\varphi^*\omega$ is regular on $F'$, and let $x'$ be a class in the two-chart Čech $H^1$ of the zero divisor for the preimages of $S_0$, $S_1$ under restriction of places along $\varphi$. Then the Serre residue pairing of $\varphi^*\omega$ with $x'$ equals the Serre residue pairing of $\omega$ with the trace $\mathrm{tr}_\varphi x'$ of $x'$.
--
--   This is the adjunction (projection) formula for the Serre-duality residue pairing along a finite map of function fields: pull-back of regular differentials is adjoint to the trace on the two-chart Čech $H^1$ of the structure sheaf. It is used in the comparison of Serre pairings for two maps that induce the same map on $H^1$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_serrePairing_pullbackAlong_eq_serrePairing_traceAlong.lean

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
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Definitions.Def_AlgebraicCurve_SerrePairing
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_DifferentialPushPull
import Definitions.Def_AlgebraicCurve_CechH1PushPull
import Definitions.Def_AlgebraicCurve_FibreResidueIdentityAlong

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open KaehlerDifferential
namespace AlgebraicCurve

theorem serrePairing_pullbackAlong_eq_serrePairing_traceAlong
    {K : Type*} {F : Type*} {F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [HasCanonicalLocalResidueKStar K F] [HasCanonicalLocalResidueKStar K F']
    [∀ v : Place K F, v.DCoordGenerates] [∀ w : Place K F', w.DCoordGenerates]
    [Nontrivial Ω[F⁄K]] [Nontrivial Ω[F'⁄K]]
    [HasCanonicalDivisor (K := K) (F := F)] [HasCanonicalDivisor (K := K) (F := F')]
    [HasPrincipalDivisors K F] [HasPrincipalDivisors K F']
    (hRT : ResidueTheorem K F) (hRT' : ResidueTheorem K F')
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (htr : TraceIntegralAlong φ hφ)
    (hfib : FibreResidueIdentityAlong φ hφ)
    {S₀ S₁ : Set (Place K F)} (hcover : S₀ ∪ S₁ = Set.univ)
    (ω : ↥(regularDifferentials K F))
    (hω' : Differential.pullbackAlong φ (ω : Ω[F⁄K]) ∈ regularDifferentials K F')
    (x' : cechH1 ((Place.restrictAlong φ hφ) ⁻¹' S₀) ((Place.restrictAlong φ hφ) ⁻¹' S₁) (0 : Divisor K F')) :
    serrePairing hRT' (preimage_restrictAlong_union_eq_univ φ hφ hcover)
        ⟨Differential.pullbackAlong φ (ω : Ω[F⁄K]), hω'⟩ x'
      = serrePairing hRT hcover ω (cechH1.traceAlong φ hφ htr S₀ S₁ x') := by sorry

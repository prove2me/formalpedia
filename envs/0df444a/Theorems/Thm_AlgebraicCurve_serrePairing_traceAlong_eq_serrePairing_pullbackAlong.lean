-- Prove2me | Theorems.Thm_AlgebraicCurve_serrePairing_traceAlong_eq_serrePairing_pullbackAlong
-- name    : AlgebraicCurve.serrePairing_traceAlong_eq_serrePairing_pullbackAlong
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/0d523b78-f7f0-5b3b-b64a-571af0341391
-- title:
--   Trace of differentials is adjoint to pull-back of Čech classes
-- statement:
--   Let $K$, $F$, $F'$ be fields with $F$ and $F'$ algebras over $K$, each equipped with a canonical local residue datum at every place (`HasCanonicalLocalResidueKStar`), with $d$ of a uniformiser spanning the differentials at every place of $F$ and of $F'$, with $\Omega_{F/K}$ nontrivial, with $F'$ a curve over $K$ (principal divisors have degree $0$, residue fields are finite over $K$, and $\Omega_{F'/K}$ is free of rank one over $F'$), with divisors of nonzero differentials and of nonzero functions available for $F$ and $F'$ as required, and assume the residue theorems $hRT$ for $F$ and $hRT'$ for $F'$: the sum of the residue terms of a nonzero differential against a constant adele vanishes. Let $\varphi : F \to F'$ be a $K$-algebra map which is integral and separable (the induced extension $F'/F$ is separable), and assume the fibre residue identity along $\varphi$: for every place $v$ of $F$, every $\omega \in \Omega_{F/K}$ and every $f' \in F'$, the sum over the places $w$ above $v$ of the residue terms of $\varphi^*\omega$ against the constant family $f'$ equals the residue term of $\omega$ against the constant family $\operatorname{Tr}_{F'/F}(f')$ at $v$. Let $S_0, S_1$ be sets of places of $F$ with $S_0 \cup S_1$ everything, let $\omega'$ be a regular differential on $F'$ (at each place, a valuation-integral multiple of $d$ of the uniformiser) whose trace $\operatorname{tr}_\varphi \omega' \in \Omega_{F/K}$ is again regular, and let $x$ lie in the two-chart Čech $H^1$ of the zero divisor for $(S_0, S_1)$ on $F$. Then the Serre pairing on $F$ of $\operatorname{tr}_\varphi \omega'$ with $x$ equals the Serre pairing on $F'$, for the cover by the preimages of $S_0$ and $S_1$ under restriction of places along $\varphi$, of $\omega'$ with the pull-back of $x$ along $\varphi$.
--
--   This is the adjunction (transfer) formula expressing that the trace map on differentials is adjoint to the pull-back of functions on $H^1$ of the structure sheaf, with respect to the residue pairing of Serre duality for curves. It is used, together with the dual adjunction for pull-back of differentials and trace of Čech classes, in the comparison of Serre pairings under a finite separable morphism of curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_serrePairing_traceAlong_eq_serrePairing_pullbackAlong.lean

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

theorem serrePairing_traceAlong_eq_serrePairing_pullbackAlong
    {K : Type*} {F : Type*} {F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [HasCanonicalLocalResidueKStar K F] [HasCanonicalLocalResidueKStar K F']
    [∀ v : Place K F, v.DCoordGenerates] [∀ w : Place K F', w.DCoordGenerates]
    [Nontrivial Ω[F⁄K]] [IsCurveOver K F']
    [HasCanonicalDivisor (K := K) (F := F)] [HasCanonicalDivisor (K := K) (F := F')]
    [HasPrincipalDivisors K F]
    (hRT : ResidueTheorem K F) (hRT' : ResidueTheorem K F')
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hsep : SeparableAlong K φ)
    (hfib : FibreResidueIdentityAlong φ hφ)
    {S₀ S₁ : Set (Place K F)} (hcover : S₀ ∪ S₁ = Set.univ)
    (ω' : ↥(regularDifferentials K F'))
    (hω : Differential.traceAlong φ (ω' : Ω[F'⁄K]) ∈ regularDifferentials K F)
    (x : cechH1 S₀ S₁ (0 : Divisor K F)) :
    serrePairing hRT hcover ⟨Differential.traceAlong φ (ω' : Ω[F'⁄K]), hω⟩ x
      = serrePairing hRT' (preimage_restrictAlong_union_eq_univ φ hφ hcover) ω'
          (cechH1.pullbackAlong φ hφ S₀ S₁ x) := by sorry

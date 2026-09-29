-- Prove2me | Theorems.Thm_AlgebraicCurve_serrePairing_traceAlong_eq_serrePairing_traceAlong_pullbackAlong_of_cechH1ToH1_eq
-- name    : AlgebraicCurve.serrePairing_traceAlong_eq_serrePairing_traceAlong_pullbackAlong_of_cechH1ToH1_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/f40818be-692e-58bb-a2b6-f5ff4476972e
-- title:
--   Correspondence adjunction for the Serre residue pairing
-- statement:
--   Let $K$, $F$, $F'$ be fields with $F$ and $F'$ algebras over $K$, each carrying canonical local residue data at every place, with $\Omega[F/K]$ and $\Omega[F'/K]$ nontrivial, a canonical divisor clause and principal divisors of degree zero, each place having a generating differential coordinate, and $F'$ a curve over $K$ (finite residue fields and $\Omega[F'/K]$ free of rank one over $F'$); assume the residue theorems $hRT$ for $F$ and $hRT'$ for $F'$, asserting that the residue sum of a constant adele against a nonzero differential vanishes. Let $\varphi_\alpha,\varphi_\beta\colon F \to F'$ be $K$-algebra maps that are integral, with the trace-integrality clause for $\varphi_\alpha$ (the field trace of $F'$ over $F$ along $\varphi_\alpha$ carries elements integral at every place above $v$ into the valuation subring of $v$), $F'$ separable over $F$ along $\varphi_\beta$, and the fibre residue identity for both maps (for each place $v$ of $F$, each $\omega \in \Omega[F/K]$ and each $f' \in F'$, the sum over the fibre of $v$ of the residue terms of the pullback of $\omega$ against the constant $f'$ equals the residue term of $\omega$ at $v$ against the constant trace of $f'$). Let $S_0 \cup S_1$ and $T_0 \cup T_1$ be two two-chart covers of the places of $F$. Let $\omega$ be a regular differential on $F$ (at each place a valuation-integral multiple of the differential coordinate) whose pullback along $\varphi_\alpha$ is regular on $F'$ and whose trace along $\varphi_\beta$ of that pullback is regular on $F$. Let $y$ lie in the two-chart Čech $H^1$ of the structure sheaf (divisor $0$) for $(T_0,T_1)$ on $F$, and $x'$ in that for the $\varphi_\alpha$-preimages of $S_0, S_1$ on $F'$, and suppose $x'$ and the $\varphi_\beta$-pullback of $y$ have the same image under the comparison maps into $H^1$ of the divisor $0$ on $F'$. Then the Serre residue pairing of $\omega$ with the $\varphi_\alpha$-trace of $x'$, computed for the cover $(S_0,S_1)$, equals the Serre residue pairing of the $\varphi_\beta$-trace of the $\varphi_\alpha$-pullback of $\omega$ with $y$, computed for the cover $(T_0,T_1)$.
--
--   This is the adjunction, with respect to the residue pairing between regular differentials and $\check H^1$ of the structure sheaf, of a correspondence written as a pair of maps $\varphi_\alpha, \varphi_\beta \colon F \to F'$: trace along $\varphi_\alpha$ composed with pullback along $\varphi_\beta$ on cohomology is adjoint to trace along $\varphi_\beta$ composed with pullback along $\varphi_\alpha$ on differentials. It is used for the compatibility of Hecke operators with the pairing on a modular curve, in the statement about the Serre pairing of a deformation class against a Hecke generator.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_serrePairing_traceAlong_eq_serrePairing_traceAlong_pullbackAlong_of_cechH1ToH1_eq.lean

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

theorem serrePairing_traceAlong_eq_serrePairing_traceAlong_pullbackAlong_of_cechH1ToH1_eq
    {K : Type*} {F : Type*} {F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [HasCanonicalLocalResidueKStar K F] [HasCanonicalLocalResidueKStar K F']
    [∀ v : Place K F, v.DCoordGenerates] [∀ w : Place K F', w.DCoordGenerates]
    [Nontrivial Ω[F⁄K]] [Nontrivial Ω[F'⁄K]] [IsCurveOver K F']
    [HasCanonicalDivisor (K := K) (F := F)] [HasCanonicalDivisor (K := K) (F := F')]
    [HasPrincipalDivisors K F] [HasPrincipalDivisors K F']
    (hRT : ResidueTheorem K F) (hRT' : ResidueTheorem K F')
    (φα φβ : F →ₐ[K] F') (hφα : φα.toRingHom.IsIntegral) (hφβ : φβ.toRingHom.IsIntegral)
    (htrα : TraceIntegralAlong φα hφα) (hsepβ : SeparableAlong K φβ)
    (hfibα : FibreResidueIdentityAlong φα hφα) (hfibβ : FibreResidueIdentityAlong φβ hφβ)
    {S₀ S₁ T₀ T₁ : Set (Place K F)} (hS : S₀ ∪ S₁ = Set.univ) (hT : T₀ ∪ T₁ = Set.univ)
    (ω : ↥(regularDifferentials K F))
    (hωα : Differential.pullbackAlong φα (ω : Ω[F⁄K]) ∈ regularDifferentials K F')
    (hωβα : Differential.traceAlong φβ (Differential.pullbackAlong φα (ω : Ω[F⁄K])) ∈ regularDifferentials K F)
    (y : cechH1 T₀ T₁ (0 : Divisor K F))
    (x' : cechH1 ((Place.restrictAlong φα hφα) ⁻¹' S₀) ((Place.restrictAlong φα hφα) ⁻¹' S₁) (0 : Divisor K F'))
    (hx' : cechH1ToH1 (preimage_restrictAlong_union_eq_univ φα hφα hS) 0 x' =
      cechH1ToH1 (preimage_restrictAlong_union_eq_univ φβ hφβ hT) 0 (cechH1.pullbackAlong φβ hφβ T₀ T₁ y)) :
    serrePairing hRT hS ω (cechH1.traceAlong φα hφα htrα S₀ S₁ x')
      = serrePairing hRT hT
          ⟨Differential.traceAlong φβ (Differential.pullbackAlong φα (ω : Ω[F⁄K])), hωβα⟩ y := by sorry

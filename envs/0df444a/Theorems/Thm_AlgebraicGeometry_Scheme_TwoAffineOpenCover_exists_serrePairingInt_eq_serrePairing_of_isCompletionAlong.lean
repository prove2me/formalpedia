-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_serrePairingInt_eq_serrePairing_of_isCompletionAlong
-- name    : AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_serrePairingInt_eq_serrePairing_of_isCompletionAlong
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/c637acbb-4095-5d36-960c-fd1f81935a46
-- title:
--   Integral Čech Serre pairing equals the function-field residue pairing
-- statement:
--   Let $k$ be a perfect field, $X$ a scheme with $\mathcal V$ a cover of $X$ by two affine opens $U_0,U_1$ with $U_0\sqcup U_1=\top$ and affine intersection, and $c:X\to\operatorname{Spec}k$ with $X$ integral, $c$ proper and smooth of relative dimension $1$. Let $\sigma:\iota\to\operatorname{Hom}(\operatorname{Spec}k,X)$ be indexed by a finite type and sectional for $(\mathcal V,c)$: each $\sigma_i$ is a section of $c$ with image in $U_0$, the ranges are pairwise disjoint and their union is the complement of $U_1$. Let $\Lambda_i$ be Laurent charts of the associated cover, i.e. ring homomorphisms $\Gamma(X,U_0\cap U_1)\to k(\!(t)\!)$ fixing constants, whose residue sum kills the range of the Čech differential on Kähler differentials; assume each $\Lambda_i$ is a completion of $\Gamma(X,U_0)$ along the restriction $\rho_0$ relative to evaluation at $\sigma_i$ (expansions of $U_0$-functions are power series, every power series is matched to each finite order, and vanishing of the first $n$ coefficients characterises the $n$-th power of the kernel of evaluation), and that some element of $\Gamma(X,U_0)$ expands to $t$. Give $F=k(X)$ the $k$-algebra structure from the generic germ of $c$, and assume: $F/k$ is a curve (principal divisors of degree zero exist, residue fields of places are finite over $k$, $\Omega_{F/k}$ is free of rank one), $d\pi_v$ spans $\Omega_{F/k}$ for every place $v$, canonical divisors exist, and $h_{RT}$ is the residue theorem for $k,F$. Then $U_0\cap U_1$ and $U_0$ are nonempty, the places centred in $U_1$ together with those centred in $U_0$ exhaust all places, the generic germ of any $s\in\Gamma(X,U_0\cap U_1)$ lies in the $L$-space of the divisor $0$ on the intersection of these two sets of places, and there exist $k$-linear maps $e_1$ from the first Čech cohomology of the structure sheaf sections of $\mathcal V$ to $\check H^1$ of the divisor $0$ for the pair (places in $U_1$, places in $U_0$), sending the class of $s$ to the class of its generic germ, and $e_\Omega$ from the zeroth Čech cohomology of the Kähler sections to the regular differentials of $F/k$, sending $\omega$ to the image of its $U_0$-component under [`AlgebraicCurve.kaehlerToFunctionField`](def/AlgebraicCurve_KaehlerToFunctionField.html#L46), such that for all such $\omega$ and all classes $x$ the integral Serre pairing $(\mathcal V.\text{cover }c).\text{serrePairingInt }\Lambda\,h_v\,\omega\,x$ — the trace pairing of the cup product against the residue sum $\sum_i\Lambda_i$-residue — equals $\operatorname{serrePairing} h_{RT}$ applied to $e_\Omega\omega$ and $e_1x$.
--
--   This is the comparison, for a smooth proper curve with a sectional two-chart cover, between the Čech-level pairing defined by summing Laurent-chart residues at the boundary sections and the adelic residue pairing of differentials against $\check H^1$ of the divisor $0$ on the function field, i.e. the concrete form of Serre duality for curves. It is used to transfer nondegeneracy of the residue pairing to the integral Čech pairing and, in that form, in the computation of the Serre pairing of a Hecke generator on a modular curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_serrePairingInt_eq_serrePairing_of_isCompletionAlong.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoChartCechSerrePairingInt
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverSectional
import Definitions.Def_AlgebraicCurve_KaehlerToFunctionField
import Definitions.Def_AlgebraicCurve_SerrePairing
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_CanonicalLocalResidueInstanceV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.TwoAffineOpenCover

theorem exists_serrePairingInt_eq_serrePairing_of_isCompletionAlong
    {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover)
    (c : X ⟶ Spec (CommRingCat.of k)) [IsIntegral X] [IsProper c] [SmoothOfRelativeDimension 1 c]
    {ι : Type w} [Fintype ι] (σ : ι → (Spec (CommRingCat.of k) ⟶ X)) (hσ : 𝒱.IsSectional c σ)
    (Λ : ι → (𝒱.cover c).LaurentChart) (hv : (𝒱.cover c).ResiduesVanishOnCoboundaries Λ)
    (hΛ : ∀ i, (Λ i).IsCompletionAlong (𝒱.cover c).ρ0
      (Scheme.TwoAffineOpenCover.sectionAlgHom (σ i) (hσ.comp_eq i) (hσ.range_subset i)))
    (hΛt : ∀ i, (Λ i).HasParameter (𝒱.cover c).ρ0) :
    letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
    ∀ [AlgebraicCurve.IsCurveOver k X.functionField]
      [∀ v : AlgebraicCurve.Place k X.functionField, v.DCoordGenerates]
      [AlgebraicCurve.HasCanonicalDivisor (K := k) (F := X.functionField)]
      (hRT : AlgebraicCurve.ResidueTheorem k X.functionField),
    ∃ (_ : Nonempty (𝒱.U0 ⊓ 𝒱.U1 : X.Opens))
      (hW : AlgebraicCurve.placesOf c 𝒱.U1 ∪ AlgebraicCurve.placesOf c 𝒱.U0 = Set.univ)
      (hgerm : ∀ s : (𝒱.cover c).A01, (X.germToFunctionField (𝒱.U0 ⊓ 𝒱.U1)).hom s ∈
        AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf c 𝒱.U1 ∩ AlgebraicCurve.placesOf c 𝒱.U0)
          (0 : AlgebraicCurve.Divisor k X.functionField))
      (e1 : (𝒱.structureSheafSections c).H1 →ₗ[k]
        AlgebraicCurve.cechH1 (AlgebraicCurve.placesOf c 𝒱.U1) (AlgebraicCurve.placesOf c 𝒱.U0)
          (0 : AlgebraicCurve.Divisor k X.functionField))
      (_ : ∀ s : (𝒱.cover c).A01, e1 (Submodule.Quotient.mk s) =
        Submodule.Quotient.mk ⟨(X.germToFunctionField (𝒱.U0 ⊓ 𝒱.U1)).hom s, hgerm s⟩)
      (eΩ : (𝒱.kaehlerSections c).H0 →ₗ[k] ↥(AlgebraicCurve.regularDifferentials k X.functionField))
      (_ : Nonempty (𝒱.U0 : X.Opens))
      (_ : ∀ ω : (𝒱.kaehlerSections c).H0,
        ((eΩ ω : ↥(AlgebraicCurve.regularDifferentials k X.functionField)) : Ω[X.functionField⁄k]) =
          AlgebraicCurve.kaehlerToFunctionField c 𝒱.U0 ω.val.1),
      ∀ (ω : (𝒱.kaehlerSections c).H0) (x : (𝒱.structureSheafSections c).H1),
        (𝒱.cover c).serrePairingInt Λ hv ω x = AlgebraicCurve.serrePairing hRT hW (eΩ ω) (e1 x) := by sorry

-- Prove2me | Theorems.Thm_AlgebraicCurve_eq_zero_of_nsmul_eq_zero_of_pic0Map_eq_zero_of_smoothOfRelativeDimension_one_liesOverPrime
-- name    : AlgebraicCurve.eq_zero_of_nsmul_eq_zero_of_pic0Map_eq_zero_of_smoothOfRelativeDimension_one_liesOverPrime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/21718cf6-d934-53af-91ea-5dfd7702cab3
-- title:
--   Reduction is injective on prime-to-p torsion in Pic⁰
-- statement:
--   Let $O$ be a valuation subring of $\overline{\mathbb Q}$ and $p$ a prime with $p$ a non-unit of $O$ (the content of `LiesOverPrime`), and let $\pi : X \to \operatorname{Spec} O$ be proper and smooth of relative dimension one. Assume $\pi$ is obtained by base change from a discrete valuation ring: $O_0$ is a domain that is a discrete valuation ring, $j : O_0 \to O$ is an injective ring homomorphism, every natural number not divisible by $p$ becomes a unit in $O_0$, $\pi_0 : X_0 \to \operatorname{Spec} O_0$ is proper, smooth of relative dimension one and geometrically integral, $\pi_0$ admits a section $\varepsilon_0$, and $e_0$ is an isomorphism of $X$ with the pullback of $\pi_0$ along $\operatorname{Spec} j$ carrying $\pi$ to the second projection. Let $F$ be a field over $\overline{\mathbb Q}$ which is essentially of finite type and satisfies `IsCurveOver` (principal divisors of degree zero exist for all nonzero elements, each place has residue field finite over the base, and $\Omega_{F/\overline{\mathbb Q}}$ is free of rank one), and let $\mathfrak M$ be a `CurveModel` for $F/\overline{\mathbb Q}$, i.e. an integral scheme proper and smooth of relative dimension one over $\operatorname{Spec}\overline{\mathbb Q}$ with function field identified with $F$ compatibly with the base, with closed points in bijection with the places of $F/\overline{\mathbb Q}$ matching stalks with valuation subrings, and with every finite set of points contained in an affine open; $e$ identifies $\mathfrak M.C$ with the generic fibre $X \times_{\operatorname{Spec} O} \operatorname{Spec}\overline{\mathbb Q}$ compatibly with the structure morphisms. Assume the residue field of $O$ is algebraically closed, and let $K$ over it, with `IsCurveOver`, together with a `CurveModel` $\mathfrak M_k$ and an isomorphism $e_k$, identify the special fibre $X \times_{\operatorname{Spec} O} \operatorname{Spec} (O/\mathfrak m)$ in the same way. Let $\mathrm{red}$ be a map from places of $F/\overline{\mathbb Q}$ to places of $K$ over the residue field such that, whenever the $\overline{\mathbb Q}$-point of $X$ attached to a place $P$ is the generic point of a section $Pt$ of $\pi$, the residue-field point attached to $\mathrm{red}\,P$ is the corresponding special point of $Pt$. Assume $\mathrm{red}$ carries degree-zero divisors to degree-zero divisors via `Finsupp.mapDomain`, and let $r : \mathrm{Pic}^0(F/\overline{\mathbb Q}) \to \mathrm{Pic}^0(K)$ be an additive map sending the class of a degree-zero divisor $D$ to the class of $\mathrm{mapDomain}\ \mathrm{red}\ D$, where $\mathrm{Pic}^0$ denotes degree-zero divisors modulo principal ones. Then for every natural number $n$ not divisible by $p$ and every class $t$ with $n \cdot t = 0$ and $r(t) = 0$, one has $t = 0$.
--
--   This is the injectivity half of the classical specialisation theorem for smooth proper relative curves: on the prime-to-$p$ torsion of the degree-zero divisor class group, reduction to the special fibre has trivial kernel. It is used in the proof of [`AlgebraicCurve.exists_constantReduction_of_smoothOfRelativeDimension_one_liesOverPrime_fixedBase`](thm.html#AlgebraicCurve.exists_constantReduction_of_smoothOfRelativeDimension_one_liesOverPrime_fixedBase), and is obtained from the relative Jacobian of the pointed curve $X_0/O_0$ together with the corresponding injectivity statement for torsion points of smooth separated relative group schemes over a Henselian local ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_eq_zero_of_nsmul_eq_zero_of_pic0Map_eq_zero_of_smoothOfRelativeDimension_one_liesOverPrime.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicCurve
open AlgebraicGeometry
open NeronModelInfra

universe v

theorem AlgebraicCurve.eq_zero_of_nsmul_eq_zero_of_pic0Map_eq_zero_of_smoothOfRelativeDimension_one_liesOverPrime

    (O : ValuationSubring (AlgebraicClosure ℚ)) (p : ℕ) (hp : p.Prime) (hO : O.LiesOverPrime p)

    (X : Scheme.{0}) (π : X ⟶ Spec (CommRingCat.of ↥O)) [IsProper π] [SmoothOfRelativeDimension 1 π]

    (O₀ : Type) [CommRing O₀] [IsDomain O₀] [IsDiscreteValuationRing O₀]
    (j : O₀ →+* ↥O) (hj : Function.Injective j)
    (hju : ∀ n : ℕ, ¬ p ∣ n → IsUnit ((n : ℕ) : O₀))
    {X₀ : Scheme.{0}} (π₀ : X₀ ⟶ Spec (CommRingCat.of O₀)) [IsProper π₀]
    [SmoothOfRelativeDimension 1 π₀] [GeometricallyIntegral π₀]
    (ε₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of O₀))) π₀)
    (e₀ : X ⟶ pullback π₀ (Spec.map (CommRingCat.ofHom j))) [IsIso e₀]
    (he₀ : e₀ ≫ pullback.snd π₀ (Spec.map (CommRingCat.ofHom j)) = π)

    (F : Type) [Field F] [Algebra (AlgebraicClosure ℚ) F] [IsCurveOver (AlgebraicClosure ℚ) F]
    [Algebra.EssFiniteType (AlgebraicClosure ℚ) F]
    (𝔐 : CurveModel (AlgebraicClosure ℚ) F)
    (e : 𝔐.C ⟶ pullback π (Spec.map (CommRingCat.ofHom O.subtype))) [IsIso e]
    (he : e ≫ pullback.snd π (Spec.map (CommRingCat.ofHom O.subtype)) = 𝔐.toBase)

    [hk : IsAlgClosed (IsLocalRing.ResidueField ↥O)]
    (K : Type) [Field K] [Algebra (IsLocalRing.ResidueField ↥O) K] [IsCurveOver (IsLocalRing.ResidueField ↥O) K]
    (𝔐k : CurveModel (IsLocalRing.ResidueField ↥O) K)
    (ek : 𝔐k.C ⟶ pullback π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)))) [IsIso ek]
    (hek : ek ≫ pullback.snd π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O))) = 𝔐k.toBase)

    (red : Place (AlgebraicClosure ℚ) F → Place (IsLocalRing.ResidueField ↥O) K)
    (hred : ∀ (P : Place (AlgebraicClosure ℚ) F) (Pt : SchemeHomOver (𝟙 (Spec (CommRingCat.of ↥O))) π),
      ((𝔐.pointEquivPlace.symm P).1 ≫ e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype))) =
        Spec.map (CommRingCat.ofHom O.subtype) ≫ Pt.1 →
      ((𝔐k.pointEquivPlace.symm (red P)).1 ≫ ek ≫ pullback.fst π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)))) =
        Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)) ≫ Pt.1)

    (hred0 : ∀ D : Divisor (AlgebraicClosure ℚ) F, D ∈ Divisor.degZero (K := AlgebraicClosure ℚ) (F := F) →
      Finsupp.mapDomain red D ∈ Divisor.degZero (K := IsLocalRing.ResidueField ↥O) (F := K))
    (r : Pic0 (AlgebraicClosure ℚ) F →+ Pic0 (IsLocalRing.ResidueField ↥O) K)
    (hr : ∀ D : Divisor.degZero (K := AlgebraicClosure ℚ) (F := F),
      r (Pic0.mk D) = Pic0.mk ⟨Finsupp.mapDomain red (D : Divisor (AlgebraicClosure ℚ) F), hred0 D D.2⟩) :
    ∀ n : ℕ, ¬ p ∣ n → ∀ t : Pic0 (AlgebraicClosure ℚ) F, n • t = 0 → r t = 0 → t = 0 := by sorry

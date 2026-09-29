-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_constantReduction_of_smoothOfRelativeDimension_one_liesOverPrime_fixedBase
-- name    : AlgebraicCurve.exists_constantReduction_of_smoothOfRelativeDimension_one_liesOverPrime_fixedBase
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/9d992f3c-6d26-5b88-928a-e6eb1fa33ad0
-- title:
--   Constant reduction from a smooth proper model over a Galois-fixed base
-- statement:
--   Let $\mathcal O$ be a valuation subring of $\overline{\mathbb Q} =$ `AlgebraicClosure ℚ` with $p$ prime and $p$ a nonunit of $\mathcal O$, let $R_0$ be a commutative ring and $i : R_0 \to \mathcal O$ a ring homomorphism fixed by the decomposition subgroup of $\mathcal O$ in $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ (for each $s$ there, the action of $s$ on $\mathcal O$ composed after $i$ is $i$). Let $\pi_1 : X_1 \to \operatorname{Spec} R_0$ be proper and smooth of relative dimension $1$, such that for every algebraically closed field $k'$ and every $i' : \mathcal O \to k'$ the pullback of $\pi_1$ along $\operatorname{Spec}(i' \circ i)$ is an integral scheme. Let $\mathcal O_0$ be a discrete valuation domain with an injective $j : \mathcal O_0 \to \mathcal O$ reflecting units, in which every integer prime to $p$ is invertible, let $\pi_0 : X_0 \to \operatorname{Spec}\mathcal O_0$ be proper, smooth of relative dimension $1$ and geometrically integral with a section $\varepsilon_0$, and let $e_0$ be an isomorphism from the pullback of $\pi_1$ along $\operatorname{Spec}(i)$ to the pullback of $\pi_0$ along $\operatorname{Spec}(j)$ commuting with the projections to $\operatorname{Spec}\mathcal O$. Let $F/\overline{\mathbb Q}$ be a field which is a curve over $\overline{\mathbb Q}$ in the sense of the project (principal divisors exist, all place residue fields are finite over $\overline{\mathbb Q}$, and $\Omega[F/\overline{\mathbb Q}]$ is free of rank one) and essentially of finite type, let $\mathfrak M$ be a `CurveModel` of $F$ over $\overline{\mathbb Q}$ (an integral scheme $\mathfrak M.C$, proper and smooth of relative dimension $1$ over $\operatorname{Spec}\overline{\mathbb Q}$, with $F$ identified with its function field compatibly with the base, and a bijection between closed points and places matching stalks with valuation subrings), and let $e : \mathfrak M.C \to X_1 \times_{R_0} \overline{\mathbb Q}$ be an isomorphism over $\operatorname{Spec}\overline{\mathbb Q}$. Finally let $\mathrm{gal}$ be a homomorphism from $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ to the group of pairs (ring automorphism of $F$, ring automorphism of $\overline{\mathbb Q}$) compatible with the algebra map, whose base component is $\sigma$ itself, and which is compatible with conjugation of $\overline{\mathbb Q}$-points: if the $\overline{\mathbb Q}$-point $y$ of $\mathfrak M.C$ maps, via $e$ and the projection to $X_1$, to the $\sigma$-conjugate of the image of $x$, then $\mathfrak M.\mathrm{pointEquivPlace}\,y = \mathrm{gal}(\sigma) \cdot \mathfrak M.\mathrm{pointEquivPlace}\,x$. The conclusion asserts the existence of a field $K$ over the residue field $k$ of $\mathcal O$, a `ConstantReduction` $\mathcal R$ of $F$ along $\mathcal O$ onto $K$ (a valuation subring of $F$ inducing $\mathcal O$ on $\overline{\mathbb Q}$, a surjection onto $K$ with kernel its maximal ideal, and a degree-preserving map on places compatible with divisors of functions), a bijection $\mathrm{pts}_k$ between places of $K/k$ and sections of $\pi_1$ over $\operatorname{Spec}$ of the residue map composed after $i$, and a homomorphism $\mathrm{galk}$ from the decomposition subgroup to the semilinear automorphisms of $K/k$, subject to seven conditions: each place $P$ of $F/\overline{\mathbb Q}$, viewed as a $\overline{\mathbb Q}$-point of $X_1$, extends to a unique $\mathcal O$-point $Pt$ of $X_1$ over $\operatorname{Spec}(i)$; for any such $Pt$, the $k$-point $\mathrm{pts}_k(\mathcal R.\mathrm{placeMap}\,P)$ is the reduction of $Pt$; the base component of $\mathrm{galk}(s)$ is the induced action of $s$ on $k$; $\mathrm{pts}_k(\mathrm{galk}(s)\cdot Q)$ is the $s$-conjugate of $\mathrm{pts}_k(Q)$; $\mathcal R.\mathrm{placeMap}$ and $\mathcal R.\mathrm{pic0Map}$ are equivariant for $\mathrm{gal}(\sigma)$ and $\mathrm{galk}(\sigma)$ for $\sigma$ in the decomposition subgroup; and $\mathcal R.\mathrm{pic0Map}$ is injective on $n$-torsion of $\mathrm{Pic}^0(\overline{\mathbb Q}, F)$ for every $n$ prime to $p$.
--
--   This is Deuring's constant reduction of a one-variable function field at a place of the constant field, obtained here from a smooth proper relative curve whose base ring is fixed by the decomposition group, so that conjugation of points by the decomposition group is meaningful and the reduction is equivariant; the final clause records injectivity of reduction on prime-to-$p$ torsion of the degree-zero divisor class group. It is used in the construction of constant reductions of Shimura curve models in the Čerednik–Drinfeld setting.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_constantReduction_of_smoothOfRelativeDimension_one_liesOverPrime_fixedBase.lean

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

open CategoryTheory CategoryTheory.Limits NeronModelInfra AlgebraicCurve
open AlgebraicGeometry

theorem AlgebraicCurve.exists_constantReduction_of_smoothOfRelativeDimension_one_liesOverPrime_fixedBase

    (O : ValuationSubring (AlgebraicClosure ℚ)) (p : ℕ) (hp : p.Prime) (hO : O.LiesOverPrime p)

    (R₀ : Type) [CommRing R₀] (i : R₀ →+* ↥O)
    (hi : ∀ s : ↥(O.decompositionSubgroup ℚ),
      (MulSemiringAction.toRingHom (↥(O.decompositionSubgroup ℚ)) ↥O s).comp i = i)

    (X₁ : Scheme.{0}) (π₁ : X₁ ⟶ Spec (CommRingCat.of R₀)) [IsProper π₁] [SmoothOfRelativeDimension 1 π₁]
    (hint : ∀ (k' : Type) [Field k'] [IsAlgClosed k'] (i' : ↥O →+* k'),
      IsIntegral (pullback π₁ (Spec.map (CommRingCat.ofHom (i'.comp i)))))

    (O₀ : Type) [CommRing O₀] [IsDomain O₀] [IsDiscreteValuationRing O₀]
    (j : O₀ →+* ↥O) (hj : Function.Injective j)
    (hju : ∀ n : ℕ, ¬ p ∣ n → IsUnit ((n : ℕ) : O₀))
    (hjloc : ∀ x : O₀, IsUnit (j x) → IsUnit x)
    {X₀ : Scheme.{0}} (π₀ : X₀ ⟶ Spec (CommRingCat.of O₀)) [IsProper π₀]
    [SmoothOfRelativeDimension 1 π₀] [GeometricallyIntegral π₀]
    (ε₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of O₀))) π₀)
    (e₀ : (pullback π₁ (Spec.map (CommRingCat.ofHom i))) ⟶ pullback π₀ (Spec.map (CommRingCat.ofHom j))) [IsIso e₀]
    (he₀ : e₀ ≫ pullback.snd π₀ (Spec.map (CommRingCat.ofHom j)) = pullback.snd π₁ (Spec.map (CommRingCat.ofHom i)))

    (F : Type) [Field F] [Algebra (AlgebraicClosure ℚ) F] [IsCurveOver (AlgebraicClosure ℚ) F]
    [Algebra.EssFiniteType (AlgebraicClosure ℚ) F]
    (𝔐 : CurveModel (AlgebraicClosure ℚ) F)
    (e : 𝔐.C ⟶ pullback π₁ (Spec.map (CommRingCat.ofHom (O.subtype.comp i)))) [IsIso e]
    (he : e ≫ pullback.snd π₁ (Spec.map (CommRingCat.ofHom (O.subtype.comp i))) = 𝔐.toBase)

    (gal : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* SemilinearAut (AlgebraicClosure ℚ) F)
    (hgal_base : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      SemilinearAut.baseAut (gal σ) = (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ))
    (hgal_pts : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      ∀ x y : {x₀ : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔐.C // x₀ ≫ 𝔐.toBase = 𝟙 _},
        y.1 ≫ e ≫ pullback.fst π₁ (Spec.map (CommRingCat.ofHom (O.subtype.comp i))) =
          Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫
            x.1 ≫ e ≫ pullback.fst π₁ (Spec.map (CommRingCat.ofHom (O.subtype.comp i))) →
        𝔐.pointEquivPlace y = gal σ • 𝔐.pointEquivPlace x) :
    ∃ (K : Type) (_ : Field K) (_ : Algebra (IsLocalRing.ResidueField ↥O) K)
      (𝓡 : ConstantReduction O F K)
      (ptsk : Place (IsLocalRing.ResidueField ↥O) K ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥O).comp i))) π₁)
      (galk : ↥(O.decompositionSubgroup ℚ) →* SemilinearAut (IsLocalRing.ResidueField ↥O) K),

      (∀ P : Place (AlgebraicClosure ℚ) F, ∃! Pt : SchemeHomOver (Spec.map (CommRingCat.ofHom i)) π₁,
          ((𝔐.pointEquivPlace.symm P).1 ≫ e ≫ pullback.fst π₁ (Spec.map (CommRingCat.ofHom (O.subtype.comp i)))) =
            Spec.map (CommRingCat.ofHom O.subtype) ≫ Pt.1) ∧

      (∀ (P : Place (AlgebraicClosure ℚ) F) (Pt : SchemeHomOver (Spec.map (CommRingCat.ofHom i)) π₁),
          ((𝔐.pointEquivPlace.symm P).1 ≫ e ≫ pullback.fst π₁ (Spec.map (CommRingCat.ofHom (O.subtype.comp i)))) =
            Spec.map (CommRingCat.ofHom O.subtype) ≫ Pt.1 →
          (ptsk (𝓡.placeMap P)).1 = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)) ≫ Pt.1) ∧

      (∀ s : ↥(O.decompositionSubgroup ℚ), SemilinearAut.baseAut (galk s) =
          MulSemiringAction.toRingAut (↥(O.decompositionSubgroup ℚ)) (IsLocalRing.ResidueField ↥O) s) ∧

      (∀ (s : ↥(O.decompositionSubgroup ℚ)) (Q : Place (IsLocalRing.ResidueField ↥O) K),
          (ptsk (galk s • Q)).1 =
            Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (↥(O.decompositionSubgroup ℚ))
              (IsLocalRing.ResidueField ↥O) s)) ≫ (ptsk Q).1) ∧

      (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ O.decompositionSubgroup ℚ) (P : Place (AlgebraicClosure ℚ) F),
          𝓡.placeMap (gal σ • P) = galk ⟨σ, hσ⟩ • 𝓡.placeMap P) ∧

      (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ O.decompositionSubgroup ℚ) (c : Pic0 (AlgebraicClosure ℚ) F),
          𝓡.pic0Map (gal σ • c) = galk ⟨σ, hσ⟩ • 𝓡.pic0Map c) ∧

      (∀ n : ℕ, ¬ p ∣ n → ∀ t : Pic0 (AlgebraicClosure ℚ) F, n • t = 0 → 𝓡.pic0Map t = 0 → t = 0) := by sorry

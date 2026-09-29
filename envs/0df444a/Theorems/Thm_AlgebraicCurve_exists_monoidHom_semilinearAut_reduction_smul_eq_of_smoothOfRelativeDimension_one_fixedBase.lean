-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_monoidHom_semilinearAut_reduction_smul_eq_of_smoothOfRelativeDimension_one_fixedBase
-- name    : AlgebraicCurve.exists_monoidHom_semilinearAut_reduction_smul_eq_of_smoothOfRelativeDimension_one_fixedBase
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/6812c6b1-4d7f-56cc-8b48-26497b2a9276
-- title:
--   Galois equivariance of reduction of places, fixed base
-- statement:
--   Let $\mathcal O$ be a valuation subring of $\overline{\mathbb Q}$ with $p$ a prime such that $p$ lies in the non-units of $\mathcal O$, and assume the residue field $k$ of $\mathcal O$ is algebraically closed; let $D$ be the decomposition subgroup of $\mathcal O$ over $\mathbb Q$ inside $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$. Let $R_0$ be a commutative ring and $i : R_0 \to \mathcal O$ a ring homomorphism fixed by $D$, in the sense that the ring homomorphism of $\mathcal O$ induced by each $s \in D$ composed with $i$ equals $i$, and let $\pi_1 : X_1 \to \operatorname{Spec} R_0$ be proper and smooth of relative dimension one. Let $F$ be a field over $\overline{\mathbb Q}$ together with a `CurveModel` $\mathfrak M$ (an integral scheme $\mathfrak M.C$ proper and smooth of relative dimension one over $\operatorname{Spec}\overline{\mathbb Q}$, an isomorphism of $F$ with its function field compatible with the base, and a bijection `placeOfPoint` from closed points onto the places of $F/\overline{\mathbb Q}$, a place being a proper valuation subring containing $\overline{\mathbb Q}$ whose ring is a principal ideal ring, matching stalks, with every finite set of points contained in an affine open), and let $e$ be an isomorphism from $\mathfrak M.C$ onto the pullback of $\pi_1$ along $\operatorname{Spec}$ of $R_0 \to \mathcal O \hookrightarrow \overline{\mathbb Q}$ carrying $\mathfrak M.\mathrm{toBase}$ to the second projection. Let $\mathrm{gal}$ be a monoid homomorphism from $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ to the group `SemilinearAut` of pairs $(\text{ring automorphism of } F, \text{ring automorphism of } \overline{\mathbb Q})$ compatible with the structure map, such that the base component of $\mathrm{gal}(\sigma)$ is $\sigma$, and such that $\mathrm{gal}$ acts on places by conjugating $\overline{\mathbb Q}$-points: whenever two sections $x, y$ of $\mathfrak M.\mathrm{toBase}$ satisfy $y$ followed by $e$ and the first projection $=$ $\operatorname{Spec}\sigma$ followed by $x$, $e$ and the first projection, then `pointEquivPlace` $y = \mathrm{gal}(\sigma) \cdot$ `pointEquivPlace` $x$. Let $K$ be a field over $k$ with a `CurveModel` $\mathfrak M_k$ and an isomorphism $e_k$ onto the pullback of $\pi_1$ along $\operatorname{Spec}$ of $R_0 \to \mathcal O \to k$, again carrying $\mathfrak M_k.\mathrm{toBase}$ to the second projection. Finally let $\mathrm{red}$ be a map from places of $F/\overline{\mathbb Q}$ to places of $K/k$ pinned by lifts: every place $P$ has an $\mathcal O$-point $Pt$ of $X_1$ over $\operatorname{Spec} i$ through which the $\overline{\mathbb Q}$-point attached to $P$ factors via $\operatorname{Spec}(\mathcal O \hookrightarrow \overline{\mathbb Q})$, and for every such $Pt$ the $k$-point attached to $\mathrm{red}(P)$ is $\operatorname{Spec}$ of the residue map followed by $Pt$. Then there is a monoid homomorphism $\mathrm{galk}$ from $D$ to the semilinear automorphism group of $K$ over $k$ whose base component at $s$ is the residual action of $s$ on $k$, which acts on places of $K$ by conjugating $k$-points of $X_1$ in the same sense as above, and which satisfies $\mathrm{red}(\mathrm{gal}(\sigma) \cdot P) = \mathrm{galk}(\sigma) \cdot \mathrm{red}(P)$ for all $\sigma \in D$ and all places $P$ of $F/\overline{\mathbb Q}$.
--
--   This is the Galois-theoretic half of the reduction theory for a smooth proper relative curve over a base fixed by a decomposition group: the decomposition group of $\mathcal O$ acts semilinearly on the function field of the special fibre, and the reduction map on places is equivariant for this action, as in the classical reduction of algebraic function fields modulo a prime divisor of the constant field. It is the ingredient supplying the Galois block of [`AlgebraicCurve.exists_constantReduction_of_smoothOfRelativeDimension_one_liesOverPrime_fixedBase`](thm.html#AlgebraicCurve.exists_constantReduction_of_smoothOfRelativeDimension_one_liesOverPrime_fixedBase).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_monoidHom_semilinearAut_reduction_smul_eq_of_smoothOfRelativeDimension_one_fixedBase.lean

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

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra AlgebraicCurve

theorem AlgebraicCurve.exists_monoidHom_semilinearAut_reduction_smul_eq_of_smoothOfRelativeDimension_one_fixedBase
    (O : ValuationSubring (AlgebraicClosure ℚ)) (p : ℕ) (hp : p.Prime) (hO : O.LiesOverPrime p)
    [hk : IsAlgClosed (IsLocalRing.ResidueField ↥O)]

    (R₀ : Type) [CommRing R₀] (i : R₀ →+* ↥O)
    (hi : ∀ s : ↥(O.decompositionSubgroup ℚ),
      (MulSemiringAction.toRingHom (↥(O.decompositionSubgroup ℚ)) ↥O s).comp i = i)
    (X₁ : Scheme.{0}) (π₁ : X₁ ⟶ Spec (CommRingCat.of R₀)) [IsProper π₁] [SmoothOfRelativeDimension 1 π₁]

    (F : Type) [Field F] [Algebra (AlgebraicClosure ℚ) F]
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
        𝔐.pointEquivPlace y = gal σ • 𝔐.pointEquivPlace x)

    (K : Type) [Field K] [Algebra (IsLocalRing.ResidueField ↥O) K]
    (𝔐k : CurveModel (IsLocalRing.ResidueField ↥O) K)
    (ek : 𝔐k.C ⟶ pullback π₁ (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥O).comp i)))) [IsIso ek]
    (hek : ek ≫ pullback.snd π₁ (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥O).comp i))) = 𝔐k.toBase)

    (red : Place (AlgebraicClosure ℚ) F → Place (IsLocalRing.ResidueField ↥O) K)
    (hlift : ∀ P : Place (AlgebraicClosure ℚ) F, ∃ Pt : SchemeHomOver (Spec.map (CommRingCat.ofHom i)) π₁,
      ((𝔐.pointEquivPlace.symm P).1 ≫ e ≫ pullback.fst π₁ (Spec.map (CommRingCat.ofHom (O.subtype.comp i)))) =
        Spec.map (CommRingCat.ofHom O.subtype) ≫ Pt.1)
    (hred : ∀ (P : Place (AlgebraicClosure ℚ) F) (Pt : SchemeHomOver (Spec.map (CommRingCat.ofHom i)) π₁),
      ((𝔐.pointEquivPlace.symm P).1 ≫ e ≫ pullback.fst π₁ (Spec.map (CommRingCat.ofHom (O.subtype.comp i)))) =
        Spec.map (CommRingCat.ofHom O.subtype) ≫ Pt.1 →
      ((𝔐k.pointEquivPlace.symm (red P)).1 ≫ ek ≫
          pullback.fst π₁ (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥O).comp i)))) =
        Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)) ≫ Pt.1) :
    ∃ galk : ↥(O.decompositionSubgroup ℚ) →* SemilinearAut (IsLocalRing.ResidueField ↥O) K,

      (∀ s : ↥(O.decompositionSubgroup ℚ), SemilinearAut.baseAut (galk s) =
          MulSemiringAction.toRingAut (↥(O.decompositionSubgroup ℚ)) (IsLocalRing.ResidueField ↥O) s) ∧

      (∀ (s : ↥(O.decompositionSubgroup ℚ))
        (x y : {x₀ : Spec (CommRingCat.of (IsLocalRing.ResidueField ↥O)) ⟶ 𝔐k.C // x₀ ≫ 𝔐k.toBase = 𝟙 _}),
        y.1 ≫ ek ≫ pullback.fst π₁ (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥O).comp i))) =
          Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (↥(O.decompositionSubgroup ℚ))
              (IsLocalRing.ResidueField ↥O) s)) ≫
            x.1 ≫ ek ≫ pullback.fst π₁ (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥O).comp i))) →
        𝔐k.pointEquivPlace y = galk s • 𝔐k.pointEquivPlace x) ∧

      (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ O.decompositionSubgroup ℚ)
        (P : Place (AlgebraicClosure ℚ) F),
        red (gal σ • P) = galk ⟨σ, hσ⟩ • red P) := by sorry

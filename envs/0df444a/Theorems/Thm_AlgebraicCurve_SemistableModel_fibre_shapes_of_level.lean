-- Prove2me | Theorems.Thm_AlgebraicCurve_SemistableModel_fibre_shapes_of_level
-- name    : AlgebraicCurve.SemistableModel.fibre_shapes_of_level
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/3051e4fb-494a-5b30-a11b-b9bc1271d2e2
-- title:
--   Fibres of a semistable model over a finite level
-- statement:
--   Let $L$ be an algebraically closed field, $A \subseteq L$ a valuation subring, $F/L$ a field extension, and let $\bar F_i$ ($i \in \iota_V$) be fields over the residue field of $A$, equipped with component charts $C_i$, annuli $An_e$ ($e \in \iota_E$) with source and target maps $\mathrm{src},\mathrm{tgt}$ and places $x_s(e), x_t(e)$ of the relevant $\bar F_i$ over the residue field of $A$; here a place of a field extension is a valuation subring containing the base field, proper and a principal ideal ring. Let $M$ be a semistable model for these data: an integral scheme $X = M.X$, proper, flat and locally of finite presentation over $\operatorname{Spec} A$, with an identification $F \cong K(X)$ compatible with $A$ and with the classification of the points of $X$ as the generic point, the points $M.\mathrm{pt}(P)$ for places $P$ of $F/L$, the component generic points, the smooth special points and the nodes. Assume $A$ has rank one, in the form: for every $x \in L^{\times}$ and every $y$ in the maximal ideal of $A$ there is $n$ with $v(y^n) \le v(x)$. Let $A_1$ be a local ring whose maximal ideal contains a nonzero element, $\iota_1 : A_1 \to A$ an injective local homomorphism such that $A_1 \to A \to A/\mathfrak m_A$ is surjective, $X_1$ an integral scheme with a morphism $f_1 : X_1 \to \operatorname{Spec} A_1$, and $e_1$ an isomorphism $M.X \cong X_1 \times_{\operatorname{Spec} A_1} \operatorname{Spec} A$ whose composite with the second projection is $M.\mathrm{toBase}$. Write $\pi$ for $e_1$ followed by the first projection. Assume further a subfield $F_1 \subseteq F$ with an isomorphism $\varphi_1 : F_1 \cong K(X_1)$ such that $F/F_1$ is algebraic, and that $\pi$ carries the generic point of $X$ to the generic point of $X_1$ and induces, on stalks at the generic points, the inclusion $F_1 \subseteq F$ through $\varphi_1$ and $M.\mathrm{ffEquiv}$. Then: (i) if $\pi(x') = \pi(x)$ and $x$ lies over the closed point of $A$, then $x' = x$; (ii) the $\pi$-fibre of $\pi(\xi_X)$ is $\{\xi_X\}$, where $\xi_X$ is the generic point of $X$; (iii) for every place $P$ of $F/L$, any $x'$ with $\pi(x') = \pi(M.\mathrm{pt}(P))$ equals $M.\mathrm{pt}(P')$ for some place $P'$; and (iv) if $\pi$ is a closed map and the fibre of $f_1$ over the closed point of $A_1$ is preconnected, then so is the fibre of $M.\mathrm{toBase}$ over the closed point of $A$.
--
--   This is the point-set comparison used when a semistable model over a rank-one valuation ring is realised as the base change of a model over a local ring of finite level: the projection to the finite-level model is injective on the special fibre, separates the generic point, preserves the class of generic-fibre points, and transfers preconnectedness of the special fibre. It is invoked in the construction of Cartier data at finite Kummer level from Cartier data on a semistable model, both in the divisor and in the balanced form, and it rests on the comparison of the two pullbacks along residue maps provided by [`AlgebraicGeometry.exists_iso_pullback_residue_of_iso_pullback`](thm.html#AlgebraicGeometry.exists_iso_pullback_residue_of_iso_pullback).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_SemistableModel_fibre_shapes_of_level.lean

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_SemistableModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve

universe u u'

theorem AlgebraicCurve.SemistableModel.fibre_shapes_of_level
    {L : Type u} [Field L] [IsAlgClosed L] {A : ValuationSubring L}
    {F : Type u'} [Field F] [Algebra L F]
    {ιV ιE : Type*} {Fbar : ιV → Type*} [∀ i, Field (Fbar i)] [∀ i, Algebra (IsLocalRing.ResidueField A) (Fbar i)]
    {C : ∀ i, ComponentChart A F (Fbar i)} {An : ιE → Annulus A F} {src tgt : ιE → ιV}
    {xs : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (src e))}
    {xt : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (tgt e))}
    (M : SemistableModel A F Fbar C An src tgt xs xt)
    (hrk : ∀ x : L, x ≠ 0 → ∀ y : ↥A, y ∈ IsLocalRing.maximalIdeal ↥A →
      ∃ n : ℕ, A.valuation ((y : L) ^ n) ≤ A.valuation x)
    (A₁ : Type u) [CommRing A₁] [IsLocalRing A₁] (hA₁ : ∃ t : A₁, t ≠ 0 ∧ t ∈ IsLocalRing.maximalIdeal A₁)
    (ι₁ : A₁ →+* A) [IsLocalHom ι₁] (hι₁ : Function.Injective ι₁)
    (hres₁ : Function.Surjective ((IsLocalRing.residue A).comp ι₁))
    (X₁ : Scheme.{u}) [IsIntegral X₁] (f₁ : X₁ ⟶ Spec (CommRingCat.of A₁))
    (e₁ : M.X ≅ pullback f₁ (Spec.map (CommRingCat.ofHom ι₁)))
    (he₁ : e₁.hom ≫ pullback.snd f₁ (Spec.map (CommRingCat.ofHom ι₁)) = M.toBase)
    (F₁ : Subfield F) (φ₁ : F₁ ≃+* X₁.functionField) (halg : Algebra.IsAlgebraic F₁ F)
    (hcompat : ∃ hgen : (e₁.hom ≫ pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base (genericPoint M.X) =
        genericPoint X₁,
      ∀ s : F₁, M.ffEquiv (s : F) =
        ((e₁.hom ≫ pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).stalkMap (genericPoint M.X)).hom
          ((X₁.presheaf.stalkSpecializes (specializes_of_eq hgen)).hom (φ₁ s))) :
    (∀ x x' : M.X, (e₁.hom ≫ pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base x' =
        (e₁.hom ≫ pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base x →
      M.toBase.base x = IsLocalRing.closedPoint ↥A → x' = x) ∧
    (∀ x' : M.X, (e₁.hom ≫ pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base x' =
        (e₁.hom ≫ pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base (genericPoint M.X) →
      x' = genericPoint M.X) ∧
    (∀ (P : Place L F) (x' : M.X), (e₁.hom ≫ pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base x' =
        (e₁.hom ≫ pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base (M.pt P) →
      ∃ P' : Place L F, x' = M.pt P') ∧
    (IsClosedMap (e₁.hom ≫ pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base →
      _root_.IsPreconnected (f₁.base ⁻¹' {IsLocalRing.closedPoint A₁}) →
      _root_.IsPreconnected (M.toBase.base ⁻¹' {IsLocalRing.closedPoint ↥A})) := by sorry

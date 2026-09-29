-- Prove2me | Theorems.Thm_AlgebraicCurve_SemistableModel_Descent_exists_isIntegral_pullback_isIntegrallyClosed_stalk_and_subfield_equiv_functionField_of_range_eq_inter
-- name    : AlgebraicCurve.SemistableModel.Descent.exists_isIntegral_pullback_isIntegrallyClosed_stalk_and_subfield_equiv_functionField_of_range_eq_inter
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/ae789d6c-2f94-5257-a913-a59dec56a998
-- title:
--   Base change of a descended semistable model along A₁
-- statement:
--   Let $L$ be an algebraically closed field, $A \subseteq L$ a valuation subring, and $F$ a field equipped with an $L$-algebra structure; fix index types $\iota_V,\iota_E$, residue-field extensions $\bar F_i$ of the residue field of $A$, component charts $C_i$, annuli $An_e$, source and target maps $\mathrm{src},\mathrm{tgt}$ and places $x_s,x_t$, and let $M$ be a semistable model for these data (an integral scheme $M.X$ proper and flat over $\operatorname{Spec} A$ together with an isomorphism $M.\mathrm{ffEquiv} : F \cong K(M.X)$ and the classification of points by places, components, smooth points and nodes; the remaining axioms are summarised here) and let $D$ be a descent datum for $M$: a noetherian henselian local ring $D.A_0$ with an injective local homomorphism $D.\iota : D.A_0 \to A$ whose image in $L$ is $A \cap K_0$ for a subfield $K_0 \subseteq L$ with $L/K_0$ algebraic and with $D.A_0 \to A \to A/\mathfrak m_A$ surjective, an integral scheme $X_0$ proper and flat over $\operatorname{Spec} D.A_0$, an isomorphism $M.X \cong X_0 \times_{\operatorname{Spec} D.A_0} \operatorname{Spec} A$ over $\operatorname{Spec} A$ carrying the generic point to the generic point, and a subfield $D.F_0 \subseteq F$ with $F/D.F_0$ algebraic and an isomorphism $D.F_0 \cong K(X_0)$ compatible with $M.\mathrm{ffEquiv}$. Let $A_1$ be a commutative ring, $j : D.A_0 \to A_1$ a ring homomorphism, and $\iota_1 : A_1 \to A$ an injective local homomorphism with $\iota_1 \circ j = D.\iota$, such that the image of $A_1$ in $L$ equals $A \cap K_1$ for a subfield $K_1 \subseteq L$. Then there exist a scheme $X_1$ which is integral and a morphism $f_1 : X_1 \to \operatorname{Spec} A_1$ which is proper and flat, together with an isomorphism $e_1 : M.X \cong X_1 \times_{\operatorname{Spec} A_1} \operatorname{Spec} A$ such that $e_1$ followed by the second projection is $M.\mathrm{toBase}$, every local ring of $X_1$ is integrally closed, and there exist a subfield $F_1 \subseteq F$ and a ring isomorphism $\varphi_1 : F_1 \cong K(X_1)$ with $D.F_0 \subseteq F_1$, with the image of $K_1$ in $F$ contained in $F_1$, with $F/F_1$ algebraic, and such that the composite of $e_1$ with the first projection sends the generic point of $M.X$ to the generic point of $X_1$ and, for every $s \in F_1$, $M.\mathrm{ffEquiv}(s)$ is the image of $\varphi_1(s)$ under the induced map on stalks at the generic point (composed with the specialisation map identifying the relevant stalk).
--
--   This is the base change of a descended semistable model from the henselian local ring $A_0$ to an intermediate ring $A_1$ whose image in $L$ is $A \cap K_1$, with the accompanying identification of $K(X_1)$ as a subfield $F_1$ of $F$ containing $F_0$ and $K_1$ over which $F$ is algebraic; no noetherian or henselian hypothesis on $A_1$ is imposed. It relies on [`AlgebraicCurve.SemistableModel.isIntegrallyClosed_stalk`](thm.html#AlgebraicCurve.SemistableModel.isIntegrallyClosed_stalk) together with descent of integrality and integral closedness along a flat local homomorphism, and it is used in the principality criteria for divisors on a semistable model, namely [`AlgebraicCurve.mem_principal_of_zsmul_mem_principal_of_forall_mapDomain_placeMap_eq_zero_of_genusFF_of_semistableModel_of_descent`](thm.html#AlgebraicCurve.mem_principal_of_zsmul_mem_principal_of_forall_mapDomain_placeMap_eq_zero_of_genusFF_of_semistableModel_of_descent) and [`AlgebraicCurve.sum_mem_principal_of_zsmul_mem_principal_of_isNodalPrincipal_mapDomain_placeMap_of_semistableModel_of_descent`](thm.html#AlgebraicCurve.sum_mem_principal_of_zsmul_mem_principal_of_isNodalPrincipal_mapDomain_placeMap_of_semistableModel_of_descent).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_SemistableModel_Descent_exists_isIntegral_pullback_isIntegrallyClosed_stalk_and_subfield_equiv_functionField_of_range_eq_inter.lean

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

theorem AlgebraicCurve.SemistableModel.Descent.exists_isIntegral_pullback_isIntegrallyClosed_stalk_and_subfield_equiv_functionField_of_range_eq_inter
    {L : Type u} [Field L] [IsAlgClosed L] {A : ValuationSubring L}
    {F : Type u'} [Field F] [Algebra L F]
    {ιV ιE : Type*} {Fbar : ιV → Type*} [∀ i, Field (Fbar i)] [∀ i, Algebra (IsLocalRing.ResidueField A) (Fbar i)]
    {C : ∀ i, ComponentChart A F (Fbar i)} {An : ιE → Annulus A F} {src tgt : ιE → ιV}
    {xs : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (src e))}
    {xt : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (tgt e))}
    (M : SemistableModel A F Fbar C An src tgt xs xt) (D : M.Descent)
    (A₁ : Type u) [CommRing A₁] (j : D.A₀ →+* A₁) (ι₁ : A₁ →+* A) [IsLocalHom ι₁]
    (hι₁ : Function.Injective ι₁) (hcomp : ι₁.comp j = D.ι)
    (K₁ : Subfield L) (range_ι₁ : Set.range (fun a : A₁ => ((ι₁ a : A) : L)) = (A : Set L) ∩ (K₁ : Set L)) :
    ∃ (X₁ : Scheme.{u}) (_ : IsIntegral X₁) (f₁ : X₁ ⟶ Spec (CommRingCat.of A₁)) (_ : IsProper f₁) (_ : Flat f₁)
      (e₁ : M.X ≅ pullback f₁ (Spec.map (CommRingCat.ofHom ι₁))),
      e₁.hom ≫ pullback.snd f₁ (Spec.map (CommRingCat.ofHom ι₁)) = M.toBase ∧
      (∀ x : X₁, IsIntegrallyClosed (X₁.presheaf.stalk x)) ∧
    ∃ (F₁ : Subfield F) (φ₁ : F₁ ≃+* X₁.functionField),
      (D.F₀ ≤ F₁) ∧ (∀ x : L, x ∈ K₁ → algebraMap L F x ∈ F₁) ∧ Algebra.IsAlgebraic F₁ F ∧
      (∃ hgen : (e₁.hom ≫ pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base (genericPoint M.X) =
          genericPoint X₁,
        ∀ s : F₁, M.ffEquiv (s : F) =
          ((e₁.hom ≫ pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).stalkMap (genericPoint M.X)).hom
            ((X₁.presheaf.stalkSpecializes (specializes_of_eq hgen)).hom (φ₁ s))) := by sorry

-- Prove2me | Theorems.Thm_AlgebraicGeometry_TwoGluedProjectiveLines_exists_twoAffineOpenCover_presentation_comp_iso
-- name    : AlgebraicGeometry.TwoGluedProjectiveLines.exists_twoAffineOpenCover_presentation_comp_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/aa830101-d0ac-5a6b-8640-335c391137f4
-- title:
--   Two-glued-lines presentation transports along an isomorphism of k-schemes
-- statement:
--   Let $k$ be a field, and let $x : X \to \operatorname{Spec} k$ and $x' : X' \to \operatorname{Spec} k$ be schemes over $k$, together with an isomorphism $\varphi : X \cong X'$ over $k$, i.e. $x' \circ \varphi = x$. Let $M_1, M_2$ be curve models of $\mathrm{RatFunc}(k)$ over $k$ (each an integral scheme $M_j.C$ with a proper, smooth of relative dimension $1$ structure morphism $M_j.\mathrm{toBase}$ to $\operatorname{Spec} k$, a ring isomorphism of $\mathrm{RatFunc}(k)$ with the function field of $M_j.C$ compatible with $k$, a bijection `placeEquiv` from the closed points of $M_j.C$ onto the places of $\mathrm{RatFunc}(k)$ over $k$ matching stalks with valuation subrings, and the property that every finite set of points lies in an affine open). Let $i_1 : M_1.C \to X$ and $i_2 : M_2.C \to X$ be closed immersions with $x \circ i_j = M_j.\mathrm{toBase}$ whose images cover $X$ as a set. Let $n \in \mathbb{N}$ and $a, b : \mathrm{Fin}\,n \to k^{\times}$ be such that, for each $i$, $i_1$ sends the closed point of $M_1.C$ corresponding to the place $\mathrm{placeOfPoint}(a_i)$ (the place of $k(t)$ attached to the irreducible polynomial $t - a_i$) to the same point of $X$ as $i_2$ sends the closed point corresponding to $\mathrm{placeOfPoint}(b_i)$, and such that conversely every pair $(p,q)$ with $i_1(p) = i_2(q)$ is of this form; assume the pullback $M_1.C \times_X M_2.C$ is reduced. Let $\mathcal{W}_0$ be a two-affine open cover of $X$ (affine opens $U_0, U_1$ with affine intersection and $U_0 \sqcup U_1 = \top$) such that, for $j = 1, 2$, the preimage $i_j^{-1}U_0$ is the complement of the closed point of $M_j.C$ corresponding to the place at infinity and $i_j^{-1}U_1$ is the complement of the closed point corresponding to $\mathrm{placeOfPoint}(0)$. Finally let $W_1$ be an open of $X$ such that the inclusion of $i_1^{-1}W_1$ into $M_1.C$ followed by $i_1$ is an open immersion. The conclusion asserts the existence of a two-affine open cover $\mathcal{W}_0'$ of $X'$ with $U_0' = (\varphi^{-1})^{-1}U_0$ and $U_1' = (\varphi^{-1})^{-1}U_1$, such that the composites $i_j$ followed by $\varphi$ satisfy all of the above clauses verbatim over $x'$: compatibility with the structure morphisms, covering of $X'$ by the two ranges, the same $n$ node identifications given by $a$ and $b$ and no further coincidences, reducedness of the pullback of the two composites, the four descriptions of the preimages of $U_0'$ and $U_1'$ as complements of the points at infinity and at $0$, and the open-immersion property for $(\varphi^{-1})^{-1}W_1$; in addition the set underlying $(\varphi^{-1})^{-1}W_1$ is $\varphi(W_1)$ and the ranges of the composites are the $\varphi$-images of the ranges of $i_1$ and $i_2$.
--
--   This is the transport of a presentation of a $k$-scheme as two smooth proper models of $k(t)$ glued at $n$ prescribed closed points, with a node-adapted two-affine chart, along an isomorphism of $k$-schemes; the transported data are the evident ones, obtained by composing with $\varphi$ and by taking preimages under $\varphi^{-1}$. It is used to move such a presentation of a non-smooth fibre to the isomorphic fibre of a base change, in [`AlgebraicGeometry.RelPicard.exists_chart_subsingleton_H1_fibre_of_blocks_of_not_smooth`](thm.html#AlgebraicGeometry.RelPicard.exists_chart_subsingleton_H1_fibre_of_blocks_of_not_smooth).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_TwoGluedProjectiveLines_exists_twoAffineOpenCover_presentation_comp_iso.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve

theorem AlgebraicGeometry.TwoGluedProjectiveLines.exists_twoAffineOpenCover_presentation_comp_iso
    {k : Type u} [Field k] [DecidableEq (RatFunc k)] {X X' : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k)) (x' : X' ⟶ Spec (CommRingCat.of k))
    (φ : X ≅ X') (hφ : φ.hom ≫ x' = x)
    (M₁ M₂ : CurveModel k (RatFunc k)) (i₁ : M₁.C ⟶ X) (i₂ : M₂.C ⟶ X)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (hi₁ : i₁ ≫ x = M₁.toBase) (hi₂ : i₂ ≫ x = M₂.toBase)
    (hcover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ)
    {n : ℕ} (a b : Fin n → kˣ)
    (hnode : ∀ i, i₁.base (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k (a i : k))).1 =
      i₂.base (M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint k (b i : k))).1)
    (hinter : ∀ (p : M₁.C) (q : M₂.C), i₁.base p = i₂.base q →
      ∃ i, p = (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k (a i : k))).1 ∧
        q = (M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint k (b i : k))).1)
    (htrans : IsReduced (pullback i₁ i₂))
    (𝒲₀ : X.TwoAffineOpenCover)
    (hU0₁ : ((i₁ ⁻¹ᵁ 𝒲₀.U0 : M₁.C.Opens) : Set M₁.C) = {(M₁.placeEquiv.symm (RationalFunctionField.placeInfty k)).1}ᶜ)
    (hU0₂ : ((i₂ ⁻¹ᵁ 𝒲₀.U0 : M₂.C.Opens) : Set M₂.C) = {(M₂.placeEquiv.symm (RationalFunctionField.placeInfty k)).1}ᶜ)
    (hU1₁ : ((i₁ ⁻¹ᵁ 𝒲₀.U1 : M₁.C.Opens) : Set M₁.C) = {(M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k 0)).1}ᶜ)
    (hU1₂ : ((i₂ ⁻¹ᵁ 𝒲₀.U1 : M₂.C.Opens) : Set M₂.C) = {(M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint k 0)).1}ᶜ)
    (W₁ : X.Opens) [IsOpenImmersion ((i₁ ⁻¹ᵁ W₁).ι ≫ i₁)] :
    ∃ 𝒲₀' : X'.TwoAffineOpenCover,
      𝒲₀'.U0 = φ.inv ⁻¹ᵁ 𝒲₀.U0 ∧ 𝒲₀'.U1 = φ.inv ⁻¹ᵁ 𝒲₀.U1 ∧
      (i₁ ≫ φ.hom) ≫ x' = M₁.toBase ∧ (i₂ ≫ φ.hom) ≫ x' = M₂.toBase ∧
      Set.range (i₁ ≫ φ.hom).base ∪ Set.range (i₂ ≫ φ.hom).base = Set.univ ∧
      (∀ i, (i₁ ≫ φ.hom).base (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k (a i : k))).1 =
        (i₂ ≫ φ.hom).base (M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint k (b i : k))).1) ∧
      (∀ (p : M₁.C) (q : M₂.C), (i₁ ≫ φ.hom).base p = (i₂ ≫ φ.hom).base q →
        ∃ i, p = (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k (a i : k))).1 ∧
          q = (M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint k (b i : k))).1) ∧
      IsReduced (pullback (i₁ ≫ φ.hom) (i₂ ≫ φ.hom)) ∧
      (((i₁ ≫ φ.hom) ⁻¹ᵁ 𝒲₀'.U0 : M₁.C.Opens) : Set M₁.C) = {(M₁.placeEquiv.symm (RationalFunctionField.placeInfty k)).1}ᶜ ∧
      (((i₂ ≫ φ.hom) ⁻¹ᵁ 𝒲₀'.U0 : M₂.C.Opens) : Set M₂.C) = {(M₂.placeEquiv.symm (RationalFunctionField.placeInfty k)).1}ᶜ ∧
      (((i₁ ≫ φ.hom) ⁻¹ᵁ 𝒲₀'.U1 : M₁.C.Opens) : Set M₁.C) = {(M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k 0)).1}ᶜ ∧
      (((i₂ ≫ φ.hom) ⁻¹ᵁ 𝒲₀'.U1 : M₂.C.Opens) : Set M₂.C) = {(M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint k 0)).1}ᶜ ∧
      IsOpenImmersion (((i₁ ≫ φ.hom) ⁻¹ᵁ (φ.inv ⁻¹ᵁ W₁)).ι ≫ (i₁ ≫ φ.hom)) ∧
      ((φ.inv ⁻¹ᵁ W₁ : X'.Opens) : Set X') = φ.hom.base '' (W₁ : Set X) ∧
      Set.range (i₁ ≫ φ.hom).base = φ.hom.base '' Set.range i₁.base ∧
      Set.range (i₂ ≫ φ.hom).base = φ.hom.base '' Set.range i₂.base := by sorry

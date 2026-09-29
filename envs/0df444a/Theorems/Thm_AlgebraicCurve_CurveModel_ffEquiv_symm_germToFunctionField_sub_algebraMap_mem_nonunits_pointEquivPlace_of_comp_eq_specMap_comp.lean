-- Prove2me | Theorems.Thm_AlgebraicCurve_CurveModel_ffEquiv_symm_germToFunctionField_sub_algebraMap_mem_nonunits_pointEquivPlace_of_comp_eq_specMap_comp
-- name    : AlgebraicCurve.CurveModel.ffEquiv_symm_germToFunctionField_sub_algebraMap_mem_nonunits_pointEquivPlace_of_comp_eq_specMap_comp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/1411b077-79a0-5960-bb24-7e1c2a2f5681
-- title:
--   Chart coordinates agree with point coordinates modulo the place
-- statement:
--   Let $K$ be an algebraically closed field and $L$ a field equipped with a $K$-algebra structure, and let $N$ be a curve model of $L$ over $K$: a scheme $C = N.C$ which is integral, a morphism $N.toBase : C \to \operatorname{Spec} K$ which is proper and smooth of relative dimension $1$, a ring isomorphism $N.ffEquiv : L \cong K(C)$ onto the function field of $C$ carrying $\operatorname{algebraMap}_{K,L}(a)$ to the germ at the generic point of $a$ pulled back along $N.toBase$, a bijection $N.placeOfPoint$ from the closed points of $C$ onto the places of $L/K$ (valuation subrings of $L$ containing the image of $K$, distinct from $L$, and principal ideal rings) such that for each closed point $x$ the image in $L$, under $N.ffEquiv^{-1}$, of the local ring $\mathcal O_{C,x}$ inside $K(C)$ is exactly the valuation subring of $N.placeOfPoint(x)$, and the property that every finite set of points of $C$ lies in an affine open. Let $Y$ be a scheme, $f : C \to Y$ a morphism, $B$ a commutative ring and $\iota : \operatorname{Spec} B \to Y$ an open immersion, and assume the open subscheme $f^{-1}(\iota(\operatorname{Spec} B))$ of $C$ is nonempty. Let $z$ be a $K$-point of $C$, that is, a morphism $\operatorname{Spec} K \to C$ which is a section of $N.toBase$, let $\beta : B \to K$ be a ring homomorphism, and assume that $z$ followed by $f$ equals $\operatorname{Spec}(\beta)$ followed by $\iota$. Then for every $b \in B$, the element of $L$ obtained by transporting $b$ to a section of $\mathcal O_Y$ over the open image of $\iota$, pulling it back along $f$ to a section over $f^{-1}(\iota(\operatorname{Spec} B))$, taking its germ at the generic point of $C$ in $K(C)$, and applying $N.ffEquiv^{-1}$, differs from $\operatorname{algebraMap}_{K,L}(\beta(b))$ by an element of the nonunits of the valuation subring of the place $N.pointEquivPlace(z)$ attached to $z$ (the place of the closed point underlying $z$), i.e. by an element of the maximal ideal of that valuation ring.
--
--   This is one half of the dictionary between $K$-points of a smooth proper model and places of its function field: a regular function on an affine chart, read in $L$ through the identification of $L$ with $K(C)$, is regular at the place of a $K$-point lying in the chart and takes there the value prescribed by the chart coordinates of the point. It is used in the analysis of models of modular curves, where places of points must be shown to be centred at the coordinates of the corresponding points of an affine chart.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_CurveModel_ffEquiv_symm_germToFunctionField_sub_algebraMap_mem_nonunits_pointEquivPlace_of_comp_eq_specMap_comp.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve

theorem AlgebraicCurve.CurveModel.ffEquiv_symm_germToFunctionField_sub_algebraMap_mem_nonunits_pointEquivPlace_of_comp_eq_specMap_comp
    {K : Type u} [Field K] [IsAlgClosed K] {L : Type v} [Field L] [Algebra K L] (N : CurveModel K L)
    {Y : Scheme.{u}} (f : N.C ⟶ Y) {B : Type u} [CommRing B] (ι : Spec (CommRingCat.of B) ⟶ Y) [IsOpenImmersion ι]
    [Nonempty (Scheme.Opens.toScheme (f ⁻¹ᵁ (ι ''ᵁ ⊤)))]
    (z : {q : Spec (CommRingCat.of K) ⟶ N.C // q ≫ N.toBase = 𝟙 _}) (β : B →+* K)
    (hz : z.1 ≫ f = Spec.map (CommRingCat.ofHom β) ≫ ι) (b : B) :
    N.ffEquiv.symm (N.C.germToFunctionField (f ⁻¹ᵁ (ι ''ᵁ ⊤))
        ((f.app (ι ''ᵁ ⊤)).hom ((ι.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b)))) -
      algebraMap K L (β b) ∈ (N.pointEquivPlace z).toValuationSubring.nonunits := by sorry

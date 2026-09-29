-- Prove2me | Theorems.Thm_AlgebraicCurve_CurveModel_hasValue_placeOfPoint_of_sub_algebraMap_mem
-- name    : AlgebraicCurve.CurveModel.hasValue_placeOfPoint_of_sub_algebraMap_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/48fd6f06-0805-5740-9aa1-38044869a94f
-- title:
--   Chart functions evaluate to their residue at a place
-- statement:
--   Let $K$ be a field and $L$ a field equipped with a $K$-algebra structure, and let $M$ be a curve model of $L$ over $K$: an integral scheme $C = M.C$ together with a proper morphism `M.toBase` $: C \to \operatorname{Spec} K$ that is smooth of relative dimension $1$, a ring isomorphism `M.ffEquiv` $: L \xrightarrow{\sim} K(C)$ onto the function field carrying $\operatorname{im}(K \to L)$ to the germs at the generic point of the pullbacks of constants, a bijection `M.placeOfPoint` from the closed points of $C$ onto the places of $L/K$ (valuation subrings of $L$ containing $K$, proper and with principal ideals) such that for each closed point $x$ the image in $L$ of the stalk $\mathcal O_{C,x}$ inside $K(C)$ is exactly the valuation subring of `M.placeOfPoint x`, and the property that every finite set of points of $C$ lies in an affine open. Let $B$ be a commutative ring with a $K$-algebra structure and let $G : \operatorname{Spec} B \to C$ be an open immersion with $G$ followed by `M.toBase` equal to $\operatorname{Spec}$ of $\operatorname{algebraMap} K B$, the open image $G(\top)$ being nonempty. Let $z$ be a point of $\operatorname{Spec} B$, i.e. a prime ideal of $B$, whose image $G(z)$ is a closed point of $C$, and let $f \in B$, $a \in K$ satisfy $f - a \in z$. Write $\tilde f \in L$ for `M.ffEquiv.symm` applied to the germ at the generic point of the section of $\mathcal O_C$ over $G(\top)$ corresponding to $f$ under the isomorphisms $\Gamma(\operatorname{Spec} B) \cong B$ and $\Gamma(G(\top),\mathcal O_C) \cong \Gamma(\operatorname{Spec} B,\mathcal O)$. Then $\tilde f$ has value $a$ at the place $v =$ `M.placeOfPoint` $\langle G(z)\rangle$, meaning that $\tilde f$ lies in the valuation subring of $v$ and its residue in the residue field of that subring is the image of $a$.
--
--   This is the statement that a regular function on an affine chart of a smooth proper curve, read as an element of the function field, is integral at the place attached to a closed point of the chart and has residue there equal to its value at that point; it is the evaluation lemma for the abstract curve models used in this development. It is invoked in the study of $q$-expansions on modular curves, in [`ModularCurve.XHDRLevel.exists_placeOfPoint_snd_pullback_comp_mem_ssPlacesQExp`](thm.html#ModularCurve.XHDRLevel.exists_placeOfPoint_snd_pullback_comp_mem_ssPlacesQExp) and [`ModularCurve.XHDRLevel.exists_snd_pullback_comp_eq_of_mem_ssPlacesQExp`](thm.html#ModularCurve.XHDRLevel.exists_snd_pullback_comp_eq_of_mem_ssPlacesQExp).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_CurveModel_hasValue_placeOfPoint_of_sub_algebraMap_mem.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_GluedPic0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve

universe u v

theorem AlgebraicCurve.CurveModel.hasValue_placeOfPoint_of_sub_algebraMap_mem
    {K : Type u} [Field K] {L : Type v} [Field L] [Algebra K L] (M : CurveModel K L)
    {B : Type u} [CommRing B] [Algebra K B] (G : Spec (CommRingCat.of B) ⟶ M.C) [IsOpenImmersion G]
    (hG : G ≫ M.toBase = Spec.map (CommRingCat.ofHom (algebraMap K B)))
    [Nonempty (Scheme.Opens.toScheme (G ''ᵁ ⊤))]
    (z : ↥(Spec (CommRingCat.of B))) (hz : G.base z ∈ closedPoints M.C)
    (f : B) (a : K) (hfa : f - algebraMap K B a ∈ z.asIdeal) :
    (M.placeOfPoint ⟨G.base z, hz⟩).HasValue
      (M.ffEquiv.symm (M.C.germToFunctionField (G ''ᵁ ⊤)
        ((G.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of B)).inv f)))) a := by sorry

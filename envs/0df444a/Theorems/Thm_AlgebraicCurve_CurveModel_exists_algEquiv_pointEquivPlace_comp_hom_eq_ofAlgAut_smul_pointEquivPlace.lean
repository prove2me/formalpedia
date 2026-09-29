-- Prove2me | Theorems.Thm_AlgebraicCurve_CurveModel_exists_algEquiv_pointEquivPlace_comp_hom_eq_ofAlgAut_smul_pointEquivPlace
-- name    : AlgebraicCurve.CurveModel.exists_algEquiv_pointEquivPlace_comp_hom_eq_ofAlgAut_smul_pointEquivPlace
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/4539d9ee-6794-556f-8e1b-aa644a410efb
-- title:
--   Two isomorphic curve models differ by a constant-field automorphism
-- statement:
--   Let $K$ be an algebraically closed field and $L$ a field equipped with a $K$-algebra structure, and let $M$ and $M'$ be two data of type [`AlgebraicCurve.CurveModel K L`](def/AlgebraicCurve_CurveModel.html#L23), that is: each consists of a scheme $M.C$ together with a morphism $M.toBase : M.C \to \operatorname{Spec} K$, with $M.C$ integral, $M.toBase$ proper and smooth of relative dimension $1$, a ring isomorphism $M.ffEquiv : L \cong M.C.functionField$ carrying $\operatorname{algebraMap}_{K,L}(a)$ to the image of $a$ under the canonical map $K \to M.C.functionField$ induced by $M.toBase$, a bijection $M.placeOfPoint$ from the closed points of $M.C$ onto the set of places of $L$ over $K$ (valuation subrings of $L$ containing the image of $K$, different from $L$ itself, and principal ideal rings), subject to the requirement that for each closed point $x$ the image in $L$, under $M.ffEquiv^{-1}$, of the stalk at $x$ inside the function field is exactly the valuation subring of $M.placeOfPoint(x)$, and the requirement that every finite set of points of $M.C$ lies in an affine open. Assume given an isomorphism $e : M.C \cong M'.C$ of schemes with $e.hom$ followed by $M'.toBase$ equal to $M.toBase$. Then there is a $K$-algebra automorphism $\tau$ of $L$ such that for every $K$-section $x$ of $M.toBase$, i.e. every morphism $x : \operatorname{Spec} K \to M.C$ with $x$ followed by $M.toBase$ the identity, the place of $L$ attached by $M'.pointEquivPlace$ to the section $M'.toBase \circ (e.hom \circ x)$ — a section because of the compatibility of $e$ with the two base morphisms — equals the translate of $M.pointEquivPlace(x)$ by the element $\mathrm{ofAlgAut}(\tau)$ of the group $\mathrm{SemilinearAut}\,K\,L$ of pairs $(\varphi, \psi) \in \operatorname{Aut}(L) \times \operatorname{Aut}(K)$ with $\varphi \circ \operatorname{algebraMap}_{K,L} = \operatorname{algebraMap}_{K,L} \circ \psi$, namely the pair $(\tau, 1)$, acting on places.
--
--   This is the model-independence statement for the project's notion of a smooth proper curve model of a function field: an isomorphism between the underlying curves of two models over $\operatorname{Spec} K$ need not match up the two labellings of places by elements of $L$, but it does so after twisting by a single automorphism of $L$ fixing $K$, obtained from the induced isomorphism of function fields. It allows a statement formulated over an arbitrary model of a curve to be proved on a chosen convenient model; it is used in the analysis of the reduction of points on the modular curve $X_1(p)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_CurveModel_exists_algEquiv_pointEquivPlace_comp_hom_eq_ofAlgAut_smul_pointEquivPlace.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_BaseChangeGalois

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve

universe u v

theorem AlgebraicCurve.CurveModel.exists_algEquiv_pointEquivPlace_comp_hom_eq_ofAlgAut_smul_pointEquivPlace
    (K : Type u) [Field K] [IsAlgClosed K] (L : Type v) [Field L] [Algebra K L]
    (M M' : AlgebraicCurve.CurveModel K L) (e : M.C ≅ M'.C) (he : e.hom ≫ M'.toBase = M.toBase) :
    ∃ τ : L ≃ₐ[K] L,
      ∀ x : {p : Spec (CommRingCat.of K) ⟶ M.C // p ≫ M.toBase = 𝟙 _},
        M'.pointEquivPlace ⟨x.1 ≫ e.hom, by rw [Category.assoc, he]; exact x.2⟩ =
          SemilinearAut.ofAlgAut τ • M.pointEquivPlace x := by sorry

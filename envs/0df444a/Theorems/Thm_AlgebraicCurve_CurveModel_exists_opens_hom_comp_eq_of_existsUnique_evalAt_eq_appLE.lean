-- Prove2me | Theorems.Thm_AlgebraicCurve_CurveModel_exists_opens_hom_comp_eq_of_existsUnique_evalAt_eq_appLE
-- name    : AlgebraicCurve.CurveModel.exists_opens_hom_comp_eq_of_existsUnique_evalAt_eq_appLE
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/f3154c01-56ed-5ce9-b53d-73fc2fc69bce
-- title:
--   Place-wise data yield a morphism on an open subscheme
-- statement:
--   Let $F$ be a field equipped with a $\mathbb{C}$-algebra structure satisfying `IsCurveOver ℂ F` (every nonzero element of $F$ has a principal divisor of degree $0$, every place has residue field finite over $\mathbb{C}$, and $\Omega[F/\mathbb{C}]$ is free of rank $1$ over $F$), and let $M$ be a `CurveModel ℂ F`: an integral scheme $M.C$ with a proper, smooth of relative dimension $1$ morphism `M.toBase` to $\operatorname{Spec}\mathbb{C}$, a ring isomorphism of $F$ with the function field of $M.C$ over $\mathbb{C}$, a bijection `M.placeOfPoint` from the closed points of $M.C$ onto the places of $F/\mathbb{C}$ matching stalks with valuation subrings, and the property that every finite set of points lies in one affine open. Let $p_Y : Y \to \operatorname{Spec}\mathbb{C}$ be a scheme over $\mathbb{C}$, let $w$ assign to each place $v$ of $F/\mathbb{C}$ a section $(w\,v).1 : \operatorname{Spec}\mathbb{C} \to Y$ of $p_Y$, and let $U \subseteq Y$ be an affine open. Assume (A) the set of places $v$ for which $(w\,v).1$ does not factor through $U$ (i.e. $\top \le (w\,v).1^{-1}U$ fails) is finite, and (B) for every section $\varphi \in \Gamma(Y,U)$ there is a unique $\xi \in F$ such that for every place $v$ with $(w\,v).1$ factoring through $U$ one has $\xi$ in the valuation subring of $v$ and $\mathrm{evalAt}\,v\,\xi$ (the residue of $\xi$ at $v$ pulled back to $\mathbb{C}$) equal to the value of $\varphi$ at $(w\,v).1$, that is, the image of $(w\,v).1^{\sharp}\varphi$ under the isomorphism $\Gamma(\operatorname{Spec}\mathbb{C}) \cong \mathbb{C}$. Then there is an open $V \subseteq M.C$ characterised by: a point $x$ lies in $V$ if and only if, whenever $x$ is a closed point, the place $M.\mathrm{placeEquiv}(x)$ satisfies $\top \le (w\,\cdot).1^{-1}U$; and there is a morphism $W$ from the open subscheme $V$ to $Y$ with $W$ followed by $p_Y$ equal to the open immersion $V.\iota$ followed by `M.toBase`, and such that for every $\mathbb{C}$-point $p$ of $M.C$ over $\operatorname{Spec}\mathbb{C}$ and every $q : \operatorname{Spec}\mathbb{C} \to V$ with $q$ followed by $V.\iota$ equal to $p$, the composite $q$ followed by $W$ is $(w\,(M.\mathrm{pointEquivPlace}\,p)).1$.
--
--   This is the algebraic core of the passage from place-wise data on a function field to an actual morphism of schemes: a family of $\mathbb{C}$-points of $Y$ indexed by the places of $F$, whose coordinate functions in one affine chart $U$ of $Y$ come from elements of $F$, is realised by a morphism from an open subscheme of the smooth proper model $M.C$ into $Y$, agreeing with the given family on $\mathbb{C}$-points. It is used by [`AlgebraicCurve.CurveModel.existsUnique_hom_comp_eq_of_differentiableAt_appLE_of_isSeparated`](thm.html#AlgebraicCurve.CurveModel.existsUnique_hom_comp_eq_of_differentiableAt_appLE_of_isSeparated), where such local morphisms over an affine cover of a separated $Y$ are glued into a single morphism.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_CurveModel_exists_opens_hom_comp_eq_of_existsUnique_evalAt_eq_appLE.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_CurveModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve

theorem AlgebraicCurve.CurveModel.exists_opens_hom_comp_eq_of_existsUnique_evalAt_eq_appLE
    (F : Type) [Field F] [Algebra ℂ F] [IsCurveOver ℂ F]
    (M : CurveModel ℂ F)
    {Y : Scheme.{0}} (pY : Y ⟶ Spec (CommRingCat.of ℂ))
    (w : Place ℂ F → {P : Spec (CommRingCat.of ℂ) ⟶ Y // P ≫ pY = 𝟙 _})
    (U : Y.Opens) (hU : IsAffineOpen U)
    (hA : Set.Finite {v : Place ℂ F | ¬ (⊤ ≤ (w v).1 ⁻¹ᵁ U)})
    (hB : ∀ φ : Γ(Y, U), ∃! ξ : F, ∀ (v : Place ℂ F) (h : ⊤ ≤ (w v).1 ⁻¹ᵁ U),
      ξ ∈ v.toValuationSubring ∧
        Place.evalAt v ξ = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((w v).1.appLE U ⊤ h) φ)) :
    ∃ (V : M.C.Opens),
      (∀ x : M.C, x ∈ V ↔ ∀ hx : x ∈ closedPoints M.C, ⊤ ≤ (w (M.placeEquiv ⟨x, hx⟩)).1 ⁻¹ᵁ U) ∧
      ∃ W : (V : Scheme.{0}) ⟶ Y,
        W ≫ pY = V.ι ≫ M.toBase ∧
        ∀ (p : {p : Spec (CommRingCat.of ℂ) ⟶ M.C // p ≫ M.toBase = 𝟙 _})
          (q : Spec (CommRingCat.of ℂ) ⟶ (V : Scheme.{0})), q ≫ V.ι = p.1 →
          q ≫ W = (w (M.pointEquivPlace p)).1 := by sorry

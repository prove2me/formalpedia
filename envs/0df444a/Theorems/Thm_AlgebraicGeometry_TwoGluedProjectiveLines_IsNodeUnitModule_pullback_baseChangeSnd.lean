-- Prove2me | Theorems.Thm_AlgebraicGeometry_TwoGluedProjectiveLines_IsNodeUnitModule_pullback_baseChangeSnd
-- name    : AlgebraicGeometry.TwoGluedProjectiveLines.IsNodeUnitModule.pullback_baseChangeSnd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/9923bc1f-97f4-5f2f-a38d-acb11cf84199
-- title:
--   Node-unit modules are stable under base change in T
-- statement:
--   Let $\kappa$ be an algebraically closed field, $x\colon X\to\operatorname{Spec}\kappa$ a morphism with $X$ reduced, and let $M_1,M_2$ be curve models of $\mathrm{RatFunc}\,\kappa$ over $\kappa$, each consisting of an integral scheme proper and smooth of relative dimension $1$ over $\kappa$ together with an isomorphism of its function field with $\kappa(t)$ and a bijection of its closed points with the places of $\kappa(t)/\kappa$ matching stalks with valuation subrings. Let $i_1\colon M_1.C\to X$, $i_2\colon M_2.C\to X$ be closed immersions with $i_1\ \text{followed by}\ x = M_1.\mathrm{toBase}$ and likewise for $i_2$, whose set-theoretic images cover $X$. Let $a,b\colon \mathrm{Fin}\,s\to\kappa^\times$ with $a$ injective, let $\alpha_i$, $\beta_i$ denote the closed points of $M_1.C$, $M_2.C$ carrying the places of $\kappa(t)$ attached to $t-a_i$, $t-b_i$, and assume $i_1(\alpha_i)=i_2(\beta_i)$ for all $i$, that every pair $(p,q)$ with $i_1(p)=i_2(q)$ is of this form, and that $\mathrm{pullback}\ i_1\ i_2$ is reduced. Fix $h\colon T\to\operatorname{Spec}\kappa$, units $u_i\in\Gamma(T,\top)^\times$, and a module $M$ on $X\times_\kappa T$ which is invertible (locally isomorphic to the unit sheaf) and is a node-unit module for the data $(a,b,h,u)$: there exist $j_1\colon M\to (i_1\times 1_T)_*\mathcal O_{M_1.C\times_\kappa T}$ and $j_2\colon M\to (i_2\times 1_T)_*\mathcal O_{M_2.C\times_\kappa T}$ such that over every open $W$ of $X\times_\kappa T$ the map $m\mapsto (j_1(m),j_2(m))$ is injective with image exactly the pairs $(f,g)$ whose restrictions to the $i$-th node locus satisfy $f = u_i\, g$ for all $i$. Then for any $h'\colon T'\to\operatorname{Spec}\kappa$ and any $\psi\colon T'\to T$ over $\operatorname{Spec}\kappa$, the pullback of $M$ along $1_X\times\psi\colon X\times_\kappa T'\to X\times_\kappa T$ is a node-unit module for the same $a,b$ over $h'$, with gluing units the images of the $u_i$ under the map on global sections induced by $\psi$.
--
--   This is the naturality in the parameter scheme $T$ of the node-unit construction, i.e. the assertion that the boundary map $(\Gamma(T,\mathcal O_T)^\times)^s \to \operatorname{Pic}(X\times_\kappa T)$ attached to two transversally glued projective lines is compatible with base change, so that the node-unit bundles define a morphism of functors from a split torus to the relative Picard functor of the glued curve. It is used in the analysis of the relative Picard functor of such a glued curve, in particular by [`AlgebraicGeometry.TwoGluedProjectiveLines.isAlgEquivZero_of_pullback_iso_unit`](thm.html#AlgebraicGeometry.TwoGluedProjectiveLines.isAlgEquivZero_of_pullback_iso_unit).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_TwoGluedProjectiveLines_IsNodeUnitModule_pullback_baseChangeSnd.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_TwoGluedProjectiveLinesNodeUnitModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicCurve
  NeronModelInfra AlgebraicGeometry.TwoGluedProjectiveLines

theorem AlgebraicGeometry.TwoGluedProjectiveLines.IsNodeUnitModule.pullback_baseChangeSnd
    (κ : Type u) [Field κ] [IsAlgClosed κ]
    {X : Scheme.{u}} (x : X ⟶ Spec (.of κ)) [IsReduced X]
    (M₁ M₂ : CurveModel κ (RatFunc κ)) (i₁ : M₁.C ⟶ X) (i₂ : M₂.C ⟶ X)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (hi₁ : i₁ ≫ x = M₁.toBase) (hi₂ : i₂ ≫ x = M₂.toBase)
    (hcover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ)
    {s : ℕ} (a b : Fin s → κˣ) (ha : Function.Injective a)
    (hnode : ∀ i, i₁.base (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint κ (a i : κ))).1
                = i₂.base (M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint κ (b i : κ))).1)
    (hinter : ∀ p q, i₁.base p = i₂.base q →
      ∃ i, p = (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint κ (a i))).1 ∧
        q = (M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint κ (b i))).1)
    (htrans : IsReduced (pullback i₁ i₂))
    {T : Scheme.{u}} {h : T ⟶ Spec (.of κ)} {u : Fin s → Γ(T, ⊤)ˣ} {M : (pullback x h).Modules}
    (hM : Scheme.Modules.IsInvertible M) (hu : IsNodeUnitModule x M₁ M₂ i₁ i₂ hi₁ hi₂ a b h u M)
    {T' : Scheme.{u}} {h' : T' ⟶ Spec (.of κ)} (ψ : SchemeHomOver h' h) :
    IsNodeUnitModule x M₁ M₂ i₁ i₂ hi₁ hi₂ a b h'
      (fun i => Units.map ψ.1.appTop.hom.toMonoidHom (u i))
      ((Scheme.Modules.pullback (baseChangeSnd x ψ)).obj M) := by sorry

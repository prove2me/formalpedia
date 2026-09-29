-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_isInvertible_pullback_curveChange_iso_of_closedCover
-- name    : AlgebraicGeometry.Scheme.Modules.exists_isInvertible_pullback_curveChange_iso_of_closedCover
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/d92dd13d-a876-5c7b-affc-5cd8cfe87440
-- title:
--   Milnor patching of invertible modules along a base-changed closed cover
-- statement:
--   Let $k$ be a field and let $X, Y_1, Y_2, Z$ be schemes equipped with structure morphisms $x : X \to \operatorname{Spec} k$, $y_1, y_2, z$ to $\operatorname{Spec} k$, with $X$ reduced. Let $i_1$ and $i_2$ be morphisms over $\operatorname{Spec} k$, that is, morphisms $i_1 : Y_1 \to X$ and $i_2 : Y_2 \to X$ together with the identities $i_1 \circ\!\!\!\!\!-\, x = y_1$ and $i_2$ followed by $x$ equal to $y_2$, both closed immersions, such that every point of $X$ lies in the image of $i_1$ or of $i_2$; let $j_1 : Z \to Y_1$ and $j_2 : Z \to Y_2$ be morphisms over $\operatorname{Spec} k$ exhibiting $Z$ as the fibre product of $i_1$ and $i_2$ (the square $j_1, j_2, i_1, i_2$ is a pullback square). Let $t : T \to \operatorname{Spec} k$ be arbitrary, and write $f_T$ for `curveChange` of a $k$-morphism $f$ along $t$, i.e. the induced map of fibre products over $\operatorname{Spec} k$ with $T$, so that $(i_1)_T : Y_1 \times_k T \to X \times_k T$ and likewise for $i_2, j_1, j_2$; assume the hypothesis `hsq` that $(j_1)_T$ followed by $(i_1)_T$ equals $(j_2)_T$ followed by $(i_2)_T$. Let $L_1$ on $Y_1 \times_k T$ and $L_2$ on $Y_2 \times_k T$ be modules that are invertible in the sense that every point has an open neighbourhood $U$ on which the restriction of the module along $U \hookrightarrow$ the ambient scheme is isomorphic to the unit module of the sheaf of rings of $U$, and let $\varphi : (j_1)_T^{*} L_1 \cong (j_2)_T^{*} L_2$ be an isomorphism. Then there is a module $L$ on $X \times_k T$, invertible in the same sense, and isomorphisms $\alpha_1 : (i_1)_T^{*} L \cong L_1$ and $\alpha_2 : (i_2)_T^{*} L \cong L_2$ such that $(j_1)_T^{*}(\alpha_1)$ followed by $\varphi$ equals the composite of the canonical comparison isomorphism `pullbackComp` for $(j_1)_T, (i_1)_T$, the isomorphism `pullbackCongr hsq`, the inverse of `pullbackComp` for $(j_2)_T, (i_2)_T$, and $(j_2)_T^{*}(\alpha_2)$.
--
--   This is the existence half of Milnor patching (gluing of invertible modules along a two-piece closed cover whose intersection is the scheme-theoretic fibre product), in the form stable under an arbitrary base change $T \to \operatorname{Spec} k$. It supports the construction of line bundles on base changes of a curve obtained by gluing two smooth curves, and is cited in that setting by [`AlgebraicGeometry.RelPicard.exists_isAlgEquivZero_pullback_curveChange_iso_of_isAlgEquivZero_of_twoGluedSmoothCurves`](thm.html#AlgebraicGeometry.RelPicard.exists_isAlgEquivZero_pullback_curveChange_iso_of_isAlgEquivZero_of_twoGluedSmoothCurves) and [`AlgebraicGeometry.RelPicard.exists_opens_section_restrictPair_of_twoGluedSmoothCurves`](thm.html#AlgebraicGeometry.RelPicard.exists_opens_section_restrictPair_of_twoGluedSmoothCurves).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_exists_isInvertible_pullback_curveChange_iso_of_closedCover.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardPullback

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RelPicard

theorem AlgebraicGeometry.Scheme.Modules.exists_isInvertible_pullback_curveChange_iso_of_closedCover
    {k : Type u} [Field k] {X Y₁ Y₂ Z : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k)) (hXred : IsReduced X)
    (y₁ : Y₁ ⟶ Spec (CommRingCat.of k)) (y₂ : Y₂ ⟶ Spec (CommRingCat.of k)) (z : Z ⟶ Spec (CommRingCat.of k))
    (i₁ : SchemeHomOver y₁ x) (i₂ : SchemeHomOver y₂ x) [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hjs : ∀ p : X, p ∈ Set.range i₁.1.base ∨ p ∈ Set.range i₂.1.base)
    (j₁ : SchemeHomOver z y₁) (j₂ : SchemeHomOver z y₂) (hZ : IsPullback j₁.1 j₂.1 i₁.1 i₂.1)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
    (hsq : curveChange j₁.1 j₁.2 t ≫ curveChange i₁.1 i₁.2 t = curveChange j₂.1 j₂.2 t ≫ curveChange i₂.1 i₂.2 t)
    (L₁ : (Limits.pullback y₁ t).Modules) (hL₁ : Scheme.Modules.IsInvertible L₁)
    (L₂ : (Limits.pullback y₂ t).Modules) (hL₂ : Scheme.Modules.IsInvertible L₂)
    (φ : (Scheme.Modules.pullback (curveChange j₁.1 j₁.2 t)).obj L₁ ≅
      (Scheme.Modules.pullback (curveChange j₂.1 j₂.2 t)).obj L₂) :
    ∃ (L : (Limits.pullback x t).Modules), Scheme.Modules.IsInvertible L ∧
      ∃ (α₁ : (Scheme.Modules.pullback (curveChange i₁.1 i₁.2 t)).obj L ≅ L₁)
        (α₂ : (Scheme.Modules.pullback (curveChange i₂.1 i₂.2 t)).obj L ≅ L₂),
        (Scheme.Modules.pullback (curveChange j₁.1 j₁.2 t)).map α₁.hom ≫ φ.hom =
          ((Scheme.Modules.pullbackComp (curveChange j₁.1 j₁.2 t) (curveChange i₁.1 i₁.2 t)).app L).hom ≫
            ((Scheme.Modules.pullbackCongr hsq).app L).hom ≫
            ((Scheme.Modules.pullbackComp (curveChange j₂.1 j₂.2 t) (curveChange i₂.1 i₂.2 t)).app L).inv ≫
            (Scheme.Modules.pullback (curveChange j₂.1 j₂.2 t)).map α₂.hom := by sorry

-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_exists_glue_forall_isOpenImmersion_of_forall_isOpenImmersion
-- name    : AlgebraicGeometry.Scheme.exists_glue_forall_isOpenImmersion_of_forall_isOpenImmersion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/17a12bde-d014-59b5-905b-72e19008b7bc
-- title:
--   Glueing a family of schemes along a common open subscheme
-- statement:
--   Let $W$ be a scheme, let $\iota$ be a nonempty index type (in the same universe), let $U_i$ be a scheme for each $i \in \iota$, and let $f_i \colon W \to U_i$ be morphisms, each an open immersion. The assertion is that there exist a scheme $Y$ and morphisms $g_i \colon U_i \to Y$ for all $i$ such that: (i) every $g_i$ is an open immersion; (ii) the composites $f_i$ followed by $g_i$ agree for all $i, j$, i.e. $g_i \circ f_i = g_j \circ f_j$; (iii) the images of the underlying continuous maps cover $Y$, $\bigcup_i \operatorname{range}((g_i)_{\mathrm{base}}) = Y$; (iv) for $i \neq j$ the two charts meet exactly along the image of $W$, $\operatorname{range}((g_i)_{\mathrm{base}}) \cap \operatorname{range}((g_j)_{\mathrm{base}}) = \operatorname{range}((g_i \circ f_i)_{\mathrm{base}})$; and (v) $Y$ has the universal property of the wide pushout: for every scheme $Z$ and every family $h_i \colon U_i \to Z$ with $h_i \circ f_i = h_j \circ f_j$ for all $i, j$, there is a unique morphism $k \colon Y \to Z$ with $k \circ g_i = h_i$ for all $i$.
--
--   This is the glueing of a family of schemes along one common open subscheme, in existential form: $Y$ is the wide pushout of the open immersions $f_i \colon W \to U_i$, together with the expected description of its underlying topological space. It is used in the construction of models of curves, where charts are glued along a common open part, via [`NeronModelInfra.exists_model_openCover_of_forall_isClosedImmersion_pullback_lift`](thm.html#NeronModelInfra.exists_model_openCover_of_forall_isClosedImmersion_pullback_lift).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_exists_glue_forall_isOpenImmersion_of_forall_isOpenImmersion.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.exists_glue_forall_isOpenImmersion_of_forall_isOpenImmersion
    (W : Scheme.{u}) {ι : Type u} [Nonempty ι] (U : ι → Scheme.{u}) (f : ∀ i, W ⟶ U i)
    [∀ i, IsOpenImmersion (f i)] :
    ∃ (Y : Scheme.{u}) (g : ∀ i, U i ⟶ Y),
      (∀ i, IsOpenImmersion (g i)) ∧
      (∀ i j, f i ≫ g i = f j ≫ g j) ∧
      (⋃ i, Set.range (g i).base = Set.univ) ∧
      (∀ i j, i ≠ j → Set.range (g i).base ∩ Set.range (g j).base = Set.range (f i ≫ g i).base) ∧
      (∀ (Z : Scheme.{u}) (h : ∀ i, U i ⟶ Z), (∀ i j, f i ≫ h i = f j ≫ h j) →
        ∃! k : Y ⟶ Z, ∀ i, g i ≫ k = h i) := by sorry

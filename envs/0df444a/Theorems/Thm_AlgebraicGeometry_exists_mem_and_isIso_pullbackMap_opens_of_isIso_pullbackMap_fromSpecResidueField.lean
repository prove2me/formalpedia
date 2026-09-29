-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_mem_and_isIso_pullbackMap_opens_of_isIso_pullbackMap_fromSpecResidueField
-- name    : AlgebraicGeometry.exists_mem_and_isIso_pullbackMap_opens_of_isIso_pullbackMap_fromSpecResidueField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/ae72ef16-9757-5f64-ad15-0cb06a993446
-- title:
--   Fibrewise isomorphism criterion over a neighbourhood, proper flat case
-- statement:
--   Let $X$, $Y$, $Z$ be schemes (in the bottom universe), let $p : Z \to Y$ and $q : X \to Y$ be morphisms, and let $h : Z \to X$ be a morphism over $Y$, i.e. $h$ followed by $q$ equals $p$. Assume that each of $p$ and $q$ is proper, flat and locally of finite presentation. Let $y$ be a point of the underlying space of $Y$, and write $\operatorname{Spec}\kappa(y) \to Y$ for the canonical morphism `Y.fromSpecResidueField y` from the residue field at $y$. The hypothesis is that the morphism of pullbacks induced by the triple $(h, \mathrm{id}, \mathrm{id})$, namely the fibre map $$Z \times_Y \operatorname{Spec}\kappa(y) \longrightarrow X \times_Y \operatorname{Spec}\kappa(y),$$ is an isomorphism. The conclusion asserts the existence of an open subscheme $V$ of $Y$ with $y \in V$ such that the corresponding induced morphism of pullbacks along the open immersion $V.\iota$, namely $Z \times_Y V \to X \times_Y V$, is an isomorphism.
--
--   This is the fibrewise criterion for a morphism between proper flat schemes of finite presentation over a base to be an isomorphism near a point of the base: an isomorphism on the fibre at $y$ propagates to an isomorphism over an open neighbourhood of $y$. It feeds the combined statement [`AlgebraicGeometry.exists_isOpen_mem_iff_isIso_fibre_and_isIso_restrict_of_isProper_of_isProper_of_flat`](thm.html#AlgebraicGeometry.exists_isOpen_mem_iff_isIso_fibre_and_isIso_restrict_of_isProper_of_isProper_of_flat), which packages the criterion as an equivalence between fibrewise and local isomorphy.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_mem_and_isIso_pullbackMap_opens_of_isIso_pullbackMap_fromSpecResidueField.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.exists_mem_and_isIso_pullbackMap_opens_of_isIso_pullbackMap_fromSpecResidueField
    {X Y Z : Scheme.{0}} (p : Z ⟶ Y) (q : X ⟶ Y) (h : Z ⟶ X) (w : h ≫ q = p)
    [IsProper p] [Flat p] [LocallyOfFinitePresentation p]
    [IsProper q] [Flat q] [LocallyOfFinitePresentation q]
    (y : Y) (hy : IsIso (pullback.map p (Y.fromSpecResidueField y) q (Y.fromSpecResidueField y) h (𝟙 _) (𝟙 _)
          (by rw [Category.comp_id, w]) (by rw [Category.comp_id, Category.id_comp]))) :
    ∃ V : Y.Opens, y ∈ V ∧
      IsIso (pullback.map p V.ι q V.ι h (𝟙 _) (𝟙 _)
          (by rw [Category.comp_id, w]) (by rw [Category.comp_id, Category.id_comp])) := by sorry

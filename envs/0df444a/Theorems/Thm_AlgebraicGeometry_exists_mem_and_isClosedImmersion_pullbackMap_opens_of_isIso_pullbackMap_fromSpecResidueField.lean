-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_mem_and_isClosedImmersion_pullbackMap_opens_of_isIso_pullbackMap_fromSpecResidueField
-- name    : AlgebraicGeometry.exists_mem_and_isClosedImmersion_pullbackMap_opens_of_isIso_pullbackMap_fromSpecResidueField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/80a04d88-cb30-5f86-bb26-5be1e12b605e
-- title:
--   Isomorphism on one fibre gives closed immersion near that fibre
-- statement:
--   Let $X$, $Y$, $Z$ be schemes, and let $p : Z \to Y$, $q : X \to Y$ and $h : Z \to X$ be morphisms with $h$ followed by $q$ equal to $p$, so that $h$ is a morphism over $Y$. Assume both $p$ and $q$ are proper, flat and locally of finite presentation. Let $y$ be a point of $Y$, and let $\operatorname{Spec}\kappa(y) \to Y$ be the canonical morphism `Y.fromSpecResidueField y` from the residue field at $y$. The hypothesis is that the morphism of fibre products $Z \times_Y \operatorname{Spec}\kappa(y) \to X \times_Y \operatorname{Spec}\kappa(y)$ induced by $h$ and the identity of $\operatorname{Spec}\kappa(y)$ (the `pullback.map` built from $h$, $\mathbb{1}$, $\mathbb{1}$) is an isomorphism. The conclusion is that there is an open subscheme $V$ of $Y$ with $y \in V$ such that the morphism $Z \times_Y V \to X \times_Y V$ induced in the same way by $h$, the identity of $V$ and the open immersion $V.\iota$ is a closed immersion.
--
--   This is the standard localisation statement for a $Y$-morphism between two proper flat families of finite presentation: being an isomorphism on the fibre over $y$ propagates to being a closed immersion over a neighbourhood of $y$ (EGA III, 4.6.7). It is the first half of the argument for the corresponding statement with "isomorphism" in place of "closed immersion", which cites it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_mem_and_isClosedImmersion_pullbackMap_opens_of_isIso_pullbackMap_fromSpecResidueField.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.exists_mem_and_isClosedImmersion_pullbackMap_opens_of_isIso_pullbackMap_fromSpecResidueField
    {X Y Z : Scheme.{0}} (p : Z ⟶ Y) (q : X ⟶ Y) (h : Z ⟶ X) (w : h ≫ q = p)
    [IsProper p] [Flat p] [LocallyOfFinitePresentation p]
    [IsProper q] [Flat q] [LocallyOfFinitePresentation q]
    (y : Y) (hy : IsIso (pullback.map p (Y.fromSpecResidueField y) q (Y.fromSpecResidueField y) h (𝟙 _) (𝟙 _)
          (by rw [Category.comp_id, w]) (by rw [Category.comp_id, Category.id_comp]))) :
    ∃ V : Y.Opens, y ∈ V ∧
      IsClosedImmersion (pullback.map p V.ι q V.ι h (𝟙 _) (𝟙 _)
          (by rw [Category.comp_id, w]) (by rw [Category.comp_id, Category.id_comp])) := by sorry

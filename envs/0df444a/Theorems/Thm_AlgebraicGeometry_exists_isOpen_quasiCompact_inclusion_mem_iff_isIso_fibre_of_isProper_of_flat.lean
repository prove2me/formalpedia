-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_isOpen_quasiCompact_inclusion_mem_iff_isIso_fibre_of_isProper_of_flat
-- name    : AlgebraicGeometry.exists_isOpen_quasiCompact_inclusion_mem_iff_isIso_fibre_of_isProper_of_flat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/b9da8581-bfa4-5d0b-8b8c-dfb0ac6a0158
-- title:
--   Isomorphism locus of a fibrewise map is retrocompact open
-- statement:
--   Let $X$, $Y$, $Z$ be schemes (in the bottom universe), and let $p : Z \to Y$, $q : X \to Y$ and $h : Z \to X$ be morphisms of schemes with $h$ followed by $q$ equal to $p$. Assume both $p$ and $q$ are proper, flat and locally of finite presentation. Then there is an open subscheme $U$ of $Y$ such that, first, the open immersion $U.\iota : U \to Y$ is quasi-compact (i.e. $U$ is a retrocompact open of $Y$), and, second, for every point $y$ of $Y$ one has $y \in U$ if and only if the morphism of fibres induced by $h$ is an isomorphism; here the fibre morphism is the map between the pullbacks of $p$ and of $q$ along $Y$.fromSpecResidueField $y$, namely $Z \times_Y \operatorname{Spec}\kappa(y) \to X \times_Y \operatorname{Spec}\kappa(y)$ obtained from $h$ over the identity of $\operatorname{Spec}\kappa(y)$ by the universal property of the pullback. Thus the locus of points of $Y$ at which $h$ becomes an isomorphism on fibres is open with quasi-compact inclusion into $Y$.
--
--   This is the refinement of the openness of the fibrewise isomorphism locus for proper flat morphisms of finite presentation asserting additionally that this open set is retrocompact in $Y$, in the sense that its inclusion is a quasi-compact morphism. It is used in the representability of the relative scheme of morphisms (Hom-scheme) by open pieces of a Hilbert scheme, where retrocompactness supplies the quasi-compactness of the resulting representing object over the base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_isOpen_quasiCompact_inclusion_mem_iff_isIso_fibre_of_isProper_of_flat.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.exists_isOpen_quasiCompact_inclusion_mem_iff_isIso_fibre_of_isProper_of_flat
    {X Y Z : Scheme.{0}} (p : Z ⟶ Y) (q : X ⟶ Y) (h : Z ⟶ X) (w : h ≫ q = p)
    [IsProper p] [Flat p] [LocallyOfFinitePresentation p]
    [IsProper q] [Flat q] [LocallyOfFinitePresentation q] :
    ∃ U : Y.Opens, QuasiCompact U.ι ∧
      (∀ y : Y, y ∈ (U : Set Y) ↔
        IsIso (pullback.map p (Y.fromSpecResidueField y) q (Y.fromSpecResidueField y) h (𝟙 _) (𝟙 _)
          (by rw [Category.comp_id, w]) (by rw [Category.comp_id, Category.id_comp]))) := by sorry

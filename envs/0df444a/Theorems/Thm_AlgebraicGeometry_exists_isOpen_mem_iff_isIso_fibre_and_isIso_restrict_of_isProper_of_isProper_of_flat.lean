-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_isOpen_mem_iff_isIso_fibre_and_isIso_restrict_of_isProper_of_isProper_of_flat
-- name    : AlgebraicGeometry.exists_isOpen_mem_iff_isIso_fibre_and_isIso_restrict_of_isProper_of_isProper_of_flat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/63f051c0-593c-56c4-928e-f187ad835609
-- title:
--   Fibrewise isomorphism locus is open, and an isomorphism there
-- statement:
--   Let $X$, $Y$, $Z$ be schemes (in the bottom universe), let $p : Z \to Y$ and $q : X \to Y$ be morphisms, and let $h : Z \to X$ be a morphism over $Y$, i.e. $h$ followed by $q$ equals $p$. Assume that both $p$ and $q$ are proper, flat and locally of finite presentation. Then there is an open subscheme $U$ of $Y$ with the following two properties. First, a point $y$ of $Y$ lies in $U$ precisely when the morphism induced by $h$ on the base changes along $\mathrm{Spec}\,\kappa(y) \to Y$ is an isomorphism, where the induced morphism is the canonical map $Z \times_Y \mathrm{Spec}\,\kappa(y) \to X \times_Y \mathrm{Spec}\,\kappa(y)$ obtained from $h$ and the identity of $\mathrm{Spec}\,\kappa(y)$; that is, $U$ is exactly the set of points at which the fibre map $h_y \colon Z_y \to X_y$ is an isomorphism, and this set is open. Second, the morphism induced by $h$ on the base changes along the open immersion $U \to Y$, namely $Z \times_Y U \to X \times_Y U$, is an isomorphism.
--
--   This is the openness of the locus where a $Y$-morphism between two proper, flat, finitely presented $Y$-schemes is a fibrewise isomorphism, together with the statement that the morphism becomes an isomorphism after base change to that locus (as in EGA IV 17.9.1). It is used in the construction of Hom-schemes: applied to a flat closed family inside $A \times_Y B$ and the first projection it makes the condition ‘the family is a graph’ open, and it is cited by the results constructing the representing scheme for the relevant Hilbert pieces and by the associated quasi-compactness and local finiteness statements.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_isOpen_mem_iff_isIso_fibre_and_isIso_restrict_of_isProper_of_isProper_of_flat.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.exists_isOpen_mem_iff_isIso_fibre_and_isIso_restrict_of_isProper_of_isProper_of_flat
    {X Y Z : Scheme.{0}} (p : Z ⟶ Y) (q : X ⟶ Y) (h : Z ⟶ X) (w : h ≫ q = p)
    [IsProper p] [Flat p] [LocallyOfFinitePresentation p]
    [IsProper q] [Flat q] [LocallyOfFinitePresentation q] :
    ∃ U : Y.Opens,
      (∀ y : Y, y ∈ (U : Set Y) ↔
        IsIso (pullback.map p (Y.fromSpecResidueField y) q (Y.fromSpecResidueField y) h (𝟙 _) (𝟙 _)
          (by rw [Category.comp_id, w]) (by rw [Category.comp_id, Category.id_comp]))) ∧
      IsIso (pullback.map p U.ι q U.ι h (𝟙 _) (𝟙 _) (by rw [Category.comp_id, w]) (by rw [Category.comp_id, Category.id_comp])) := by sorry

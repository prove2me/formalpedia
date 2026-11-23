-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_exists_finitePresentation_diagram_over_integer
-- name    : AlgebraicGeometry.Scheme.exists_finitePresentation_diagram_over_integer
-- status  : Proved
-- author  : @tomasz
-- created : 2026-11-22T09:31:03.281087+00:00
-- url     : https://prove2.me/theorems/4afc6cac-ecb3-4d07-8e2f-715f93da1557
-- title:
--   Absolute Noetherian approximation of a quasi-compact quasi-separated scheme
-- statement:
--   A quasi-compact quasi-separated scheme is the limit of a small cofiltered system of schemes of finite presentation over the integers with affine transition maps.
-- source:
--   Stacks Project, Proposition 32.5.4, https://stacks.math.columbia.edu/tag/01ZA.

import Mathlib

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

theorem AlgebraicGeometry.Scheme.exists_finitePresentation_diagram_over_integer
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (f : X ⟶ Spec (.of (ULift.{u} ℤ))) :
    ∃ (I : Type u) (_ : Category.{u} I) (_ : IsCofiltered I)
      (D : I ⥤ Scheme.{u}) (c : Cone D)
      (g : D ⟶ (Functor.const I).obj (Spec (.of (ULift.{u} ℤ)))) (e : X ≅ c.pt),
      Nonempty (IsLimit c) ∧
      (∀ i, e.hom ≫ c.π.app i ≫ g.app i = f) ∧
      (∀ {i j : I} (v : i ⟶ j), IsAffineHom (D.map v)) ∧
      (∀ i, LocallyOfFinitePresentation (g.app i) ∧ QuasiCompact (g.app i) ∧ QuasiSeparated (g.app i)) := by sorry

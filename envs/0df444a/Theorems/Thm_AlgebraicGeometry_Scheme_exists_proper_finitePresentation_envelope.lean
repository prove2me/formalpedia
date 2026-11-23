-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_exists_proper_finitePresentation_envelope
-- name    : AlgebraicGeometry.Scheme.exists_proper_finitePresentation_envelope
-- status  : Proved
-- author  : @tomasz
-- created : 2026-11-22T07:13:14.260597+00:00
-- url     : https://prove2.me/theorems/a24612b8-52e6-4ba0-8451-4a86113a4f2e
-- title:
--   Embed a proper scheme in a proper finitely presented scheme
-- statement:
--   A proper scheme over an affine base admits a closed immersion over the base into a proper scheme of finite presentation.
-- source:
--   Stacks Project, Lemma 32.13.2, https://stacks.math.columbia.edu/tag/09ZR, taking one stage.

import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Proper

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

theorem AlgebraicGeometry.Scheme.exists_proper_finitePresentation_envelope
    {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) [IsProper f] :
    ∃ (Y : Scheme.{u}) (g : Y ⟶ Spec (.of R)) (a : X ⟶ Y),
      IsProper g ∧ LocallyOfFinitePresentation g ∧ IsClosedImmersion a ∧ a ≫ g = f := by sorry

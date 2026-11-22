-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_exists_separated_finitePresentation_envelope
-- name    : AlgebraicGeometry.Scheme.exists_separated_finitePresentation_envelope
-- status  : Open
-- author  : @tomasz
-- created : 2026-11-22T08:40:46.364937+00:00
-- url     : https://prove2.me/theorems/48a920d5-20be-48a2-b5fa-6feb03c89576
-- title:
--   Embed a separated finite-type scheme in a separated finitely presented scheme
-- statement:
--   A separated finite-type scheme over an affine base admits a closed immersion over the base into a separated finitely presented scheme.
-- source:
--   Stacks Project, Lemma 32.9.6, https://stacks.math.columbia.edu/tag/01ZJ.

import Mathlib

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

theorem AlgebraicGeometry.Scheme.exists_separated_finitePresentation_envelope
    {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ (Y : Scheme.{u}) (g : Y ⟶ Spec (.of R)) (a : X ⟶ Y),
      IsSeparated g ∧ LocallyOfFinitePresentation g ∧ QuasiCompact g ∧
        IsClosedImmersion a ∧ a ≫ g = f := by sorry

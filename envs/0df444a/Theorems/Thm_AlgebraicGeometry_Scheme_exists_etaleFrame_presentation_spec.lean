-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_exists_etaleFrame_presentation_spec
-- name    : AlgebraicGeometry.Scheme.exists_etaleFrame_presentation_spec
-- status  : Proved
-- author  : @tomasz
-- created : 2026-11-19T15:30:46.54255+00:00
-- url     : https://prove2.me/theorems/aa8bb302-de0f-40eb-bbc3-006790c2b63d
-- title:
--   Effective descent of étale units torsors on affine schemes
-- statement:
--   Every units torsor on an affine spectrum is the specified torsor of a frame presentation of an invertible module. The affine proof uses a faithfully flat étale algebra and descent of the rank-one module with the scalar cocycle.
-- source:
--   Stacks Project, Theorem 59.24.1, https://stacks.math.columbia.edu/tag/03P8.

import Definitions.Def_AlgebraicGeometry_EtaleFramePresentations

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory MonoidalCategory
open PhilipponTorsorSectionFibers PhilipponEtaleFrameTorsor PhilipponEtaleFrameSections
open PhilipponTensorFrames
universe u
open Opposite

theorem AlgebraicGeometry.Scheme.exists_etaleFrame_presentation_spec (R : CommRingCat.{u}) (A : Torsor (PhilipponKummerSequence.units (Spec R))) :
    ∃ (M : (Spec R).Modules) (_ : Scheme.Modules.IsInvertible M)
      (P : Presentation M), P.torsor = A := by sorry

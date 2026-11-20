-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_exists_etaleFrame_presentation_of_torsor
-- name    : AlgebraicGeometry.Scheme.exists_etaleFrame_presentation_of_torsor
-- status  : Proved
-- author  : @tomasz
-- created : 2026-11-19T00:05:59.744643+00:00
-- url     : https://prove2.me/theorems/ddcdbc17-c73f-4cbf-be3e-fb45e796b584
-- title:
--   Effective descent for small étale units torsors
-- statement:
--   Every torsor under the units sheaf on the small étale site of a scheme arises from an invertible module. The presentation consists of an actual map from the presheaf of frames to the given torsor, preserving differences and bijective on every object admitting a frame. This is the rank-one case of faithfully flat descent, applied to the cocycle from local sections.
-- source:
--   Stacks Project, Proposition 35.5.2, https://stacks.math.columbia.edu/tag/023T.

import Definitions.Def_AlgebraicGeometry_EtaleFramePresentations

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory MonoidalCategory
open PhilipponTorsorSectionFibers PhilipponEtaleFrameTorsor PhilipponEtaleFrameSections
open PhilipponTensorFrames
universe u

theorem AlgebraicGeometry.Scheme.exists_etaleFrame_presentation_of_torsor (X : Scheme.{u}) (A : Torsor (PhilipponKummerSequence.units X)) :
    ∃ (M : X.Modules) (_ : Scheme.Modules.IsInvertible M) (P : Presentation M), P.torsor = A := by sorry

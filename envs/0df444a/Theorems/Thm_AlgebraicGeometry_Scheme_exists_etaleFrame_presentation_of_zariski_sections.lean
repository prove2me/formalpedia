-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_exists_etaleFrame_presentation_of_zariski_sections
-- name    : AlgebraicGeometry.Scheme.exists_etaleFrame_presentation_of_zariski_sections
-- status  : Proved
-- author  : @tomasz
-- created : 2026-11-19T15:30:47.409095+00:00
-- url     : https://prove2.me/theorems/973a8830-b76b-4bc2-aaac-ed549c845467
-- title:
--   Frame presentation of a Zariski-locally trivial units torsor
-- statement:
--   Suppose every point of X belongs to an open subscheme on which the given small étale units torsor has a section. Gluing the trivial modules using the transition units gives an invertible module with a frame presentation whose torsor is the given torsor.
-- source:
--   Stacks Project, Theorem 59.24.1, https://stacks.math.columbia.edu/tag/03P8.

import Definitions.Def_AlgebraicGeometry_EtaleFramePresentations

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory MonoidalCategory
open PhilipponTorsorSectionFibers PhilipponEtaleFrameTorsor PhilipponEtaleFrameSections
open PhilipponTensorFrames
universe u
open Opposite

theorem AlgebraicGeometry.Scheme.exists_etaleFrame_presentation_of_zariski_sections (X : Scheme.{u}) (A : Torsor (PhilipponKummerSequence.units X))
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      Nonempty (A.D.P.obj (op (Scheme.Etale.mk U.ι)))) :
    ∃ (M : X.Modules) (_ : Scheme.Modules.IsInvertible M)
      (P : Presentation M), P.torsor = A := by sorry

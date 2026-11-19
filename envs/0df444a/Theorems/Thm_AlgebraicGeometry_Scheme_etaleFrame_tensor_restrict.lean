-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_etaleFrame_tensor_restrict
-- name    : AlgebraicGeometry.Scheme.etaleFrame_tensor_restrict
-- status  : Open
-- author  : @tomasz
-- created : 2026-11-19T00:05:33.663067+00:00
-- url     : https://prove2.me/theorems/62c727d4-9c1a-4076-874b-d8c9d624a265
-- title:
--   Tensoring étale frames commutes with restriction
-- statement:
--   For module frames over an étale object, tensoring them and transporting by a module isomorphism commutes with restriction along any arrow of the small étale site. The formula compares the canonical comparison for tensor products with the canonical comparison for composite pullback.
-- source:
--   Stacks Project, Section 59.24, https://stacks.math.columbia.edu/tag/03P8.

import Definitions.Def_AlgebraicGeometry_EtaleFramePresentations

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory MonoidalCategory
open PhilipponTorsorSectionFibers PhilipponEtaleFrameTorsor PhilipponEtaleFrameSections
open PhilipponTensorFrames
universe u

theorem AlgebraicGeometry.Scheme.etaleFrame_tensor_restrict {X : Scheme.{u}} {M N L : X.Modules} (e : M ⊗ N ≅ L)
    {U V : X.Etale} (f : V ⟶ U) (p : Frame M U) (q : Frame N U) :
    PhilipponEtaleFrameSections.restrict L f (tensorOn e U p q) =
      tensorOn e V (PhilipponEtaleFrameSections.restrict M f p)
        (PhilipponEtaleFrameSections.restrict N f q) := by sorry

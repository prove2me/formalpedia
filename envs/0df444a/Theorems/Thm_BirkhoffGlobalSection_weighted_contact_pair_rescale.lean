-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_weighted_contact_pair_rescale
-- name    : BirkhoffGlobalSection.weighted_contact_pair_rescale
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:40:51.96979+00:00
-- url     : https://prove2.me/theorems/2d471542-0908-4848-8d2e-e7063ef91aa7
-- title:
--   Weighted contact pair rescale
-- statement:
--   Rescaling both arguments of the displayed weighted contact exterior pairing produces the stated product of scalar factors.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained.
-- source:
--   Independent extraction of component 12 of the Proved theorem BirkhoffGlobalSection.contact_frame_basis_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_contact_frame_basis_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_contact_frame_basis_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.weighted_contact_pair_rescale :
∀ (f : Phase → ℝ) (u v w : Phase) (a b : ℝ)
    (hf : DifferentiableAt ℝ f u),
    fderiv ℝ (fun x => f x * phaseRadialContact x (b • w)) u (a • v) -
      fderiv ℝ (fun x => f x * phaseRadialContact x (a • v)) u (b • w) =
      a * b * (fderiv ℝ (fun x => f x * phaseRadialContact x w) u v -
        fderiv ℝ (fun x => f x * phaseRadialContact x v) u w) := by sorry

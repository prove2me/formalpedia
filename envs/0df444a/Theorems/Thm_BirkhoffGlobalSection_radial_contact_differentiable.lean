-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_radial_contact_differentiable
-- name    : BirkhoffGlobalSection.radial_contact_differentiable
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:51:50.609989+00:00
-- url     : https://prove2.me/theorems/755b8388-01d6-437c-b182-46bfb79681c0
-- title:
--   Radial contact differentiable
-- statement:
--   For each fixed phase vector w, the radial contact functional in its base variable is differentiable, and its differential on v is the radial contact pairing of v with w.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained.
-- source:
--   Original auxiliary result from the accepted source Solutions/Sol_BirkhoffGlobalSection_weighted_radial_contact_exterior_derivative.lean:7. Exact quantified statement retained; foundational calculus and geometry are imported from Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.

import Definitions.Def_BirkhoffGlobalSection_TransverseHopf
import Mathlib.Analysis.Calculus.FDeriv.Mul

open scoped ContDiff Topology
open BirkhoffGlobalSection Set


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.radial_contact_differentiable (u w : Phase) :
    DifferentiableAt ℝ (fun x : Phase => phaseRadialContact x w) u ∧
      (∀ v : Phase, fderiv ℝ (fun x : Phase => phaseRadialContact x w) u v =
        phaseRadialContact v w) := by sorry

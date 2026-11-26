-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_central_active_cohort_scaled_eq
-- name    : CollatzEndpointTransport.FixedTotal.central_active_cohort_scaled_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:20:43.67411+00:00
-- url     : https://prove2.me/theorems/e996e006-408b-46b9-941f-1da982c87547
-- title:
--   Fixed Total: central active cohort scaled eq
-- statement:
--   Cancellation of the exact cohort weight against the complete-level
--   normalization.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/SharpCentralRenyiPullback.lean#L444-L508
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/SharpCentralRenyiPullback.lean#L444-L508

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiPullback
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Definitions.Def_CollatzEndpointTransport_Linear_SharpCentralRenyiPullback
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.central_active_cohort_scaled_eq
    {M s : ℕ} {theta eta : ℝ} (u : Fin M)
    (hadm : CentralRenyiAdmissible (M - (u : ℕ)) s theta eta) :
    ((((3 : ℝ) ^ (s + 1)) ^ theta /
        (((sourceOddLevel M s).card : ℝ) ^ theta)) *
      (((centralLevelCohortSet M s theta eta u).card : ℝ) /
          ((sourceOddLevel M s).card : ℝ)) ^ (-theta) *
      (∑ c ∈ centralLevelCohortSet M s theta eta u,
        ((mapFiberCardAt
          (centralLevelCohortSet M s theta eta u)
          (cohortEndpoint u) c : ℕ) : ℝ) ^ theta)) =
      (3 : ℝ) ^ theta *
        (((fixedSet (M - (u : ℕ)) s).card : ℝ) *
          fixedRenyiMoment (M - (u : ℕ)) s theta) := by sorry

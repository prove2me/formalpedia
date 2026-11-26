-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralLevelCohortSet_subset_levelCohortSet
-- name    : CollatzEndpointTransport.FixedTotal.centralLevelCohortSet_subset_levelCohortSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:20:35.799361+00:00
-- url     : https://prove2.me/theorems/0748eb61-e1ad-4135-836c-d9b7e61183b8
-- title:
--   Fixed Total: central Level Cohort Set subset level Cohort Set
-- statement:
--   The Fixed Total construction uses the central Level Cohort Set subset level Cohort Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/SharpCentralRenyiPullback.lean#L416-L423
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/SharpCentralRenyiPullback.lean#L416-L423

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

theorem CollatzEndpointTransport.FixedTotal.centralLevelCohortSet_subset_levelCohortSet
    {M s : ℕ} {theta eta : ℝ} (u : Fin M) :
    centralLevelCohortSet M s theta eta u ⊆ levelCohortSet M s u := by sorry

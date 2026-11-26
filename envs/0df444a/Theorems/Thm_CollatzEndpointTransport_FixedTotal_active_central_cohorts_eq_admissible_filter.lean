-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_active_central_cohorts_eq_admissible_filter
-- name    : CollatzEndpointTransport.FixedTotal.active_central_cohorts_eq_admissible_filter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:21:16.370606+00:00
-- url     : https://prove2.me/theorems/76146306-a108-5443-ab27-11efafcd6e73
-- title:
--   Fixed Total: active central cohorts eq admissible filter
-- statement:
--   The Fixed Total construction uses the active central cohorts eq admissible filter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/SharpCentralRenyiPullback.lean#L706-L727
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/SharpCentralRenyiPullback.lean#L706-L727

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

theorem CollatzEndpointTransport.FixedTotal.active_central_cohorts_eq_admissible_filter
    (M s : ℕ) (theta eta : ℝ) :
    activeMixtureIndices (Finset.univ : Finset (Fin M))
        (centralLevelCohortSet M s theta eta) =
      admissibleCohortIndices M s theta eta := by sorry

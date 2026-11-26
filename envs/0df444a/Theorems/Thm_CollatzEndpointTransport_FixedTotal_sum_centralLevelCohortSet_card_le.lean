-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_sum_centralLevelCohortSet_card_le
-- name    : CollatzEndpointTransport.FixedTotal.sum_centralLevelCohortSet_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:21:14.8448+00:00
-- url     : https://prove2.me/theorems/d6f2e296-617c-4773-9ce0-8198c02f9af1
-- title:
--   Fixed Total: sum central Level Cohort Set card le
-- statement:
--   The Fixed Total construction uses the sum central Level Cohort Set card le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/SharpCentralRenyiPullback.lean#L425-L440
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/SharpCentralRenyiPullback.lean#L425-L440

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

theorem CollatzEndpointTransport.FixedTotal.sum_centralLevelCohortSet_card_le
    {M s : ℕ} {theta eta : ℝ} (hs : 0 < s) :
    ∑ u : Fin M, ((centralLevelCohortSet M s theta eta u).card : ℝ) ≤
      ((sourceOddLevel M s).card : ℝ) := by sorry

-- Prove2me | Theorems.Thm_FairSelling_ElevenTwelfths_MMS_agent_two
-- name    : FairSelling.ElevenTwelfths.MMS_agent_two
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:16:27.271694+00:00
-- url     : https://prove2.me/theorems/bfc6d66b-8c6f-453e-b37c-d19c4345d8b9
-- title:
--   Eleven Twelfths: MMS agent two
-- statement:
--   Agent `2` values no good, so her maximin share with selling is her proportional
--   share `36 δ`: sell everything and split the proceeds in three.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ElevenTwelfths.lean#L164-L187
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ElevenTwelfths.lean#L164-L187

import Mathlib
import Definitions.Def_RequestProject_ThreeAgents
import Definitions.Def_RequestProject_FeigeNorkin
import Definitions.Def_RequestProject_ElevenTwelfths
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.ElevenTwelfths
open FeigeNorkin

theorem FairSelling.ElevenTwelfths.MMS_agent_two {δ : ℝ} (hδ0 : 0 ≤ δ) :
    MMS 3 (instV 2) (instP δ) = 36 * δ := by sorry

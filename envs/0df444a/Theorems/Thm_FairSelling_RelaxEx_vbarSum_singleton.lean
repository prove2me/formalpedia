-- Prove2me | Theorems.Thm_FairSelling_RelaxEx_vbarSum_singleton
-- name    : FairSelling.RelaxEx.vbarSum_singleton
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:17:08.379872+00:00
-- url     : https://prove2.me/theorems/f1404c03-524d-441a-9e07-512fe626fd12
-- title:
--   Relax Ex: vbar Sum singleton
-- statement:
--   The Relax Ex construction uses the vbar Sum singleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EnvyRelaxation.lean#L54-L55
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EnvyRelaxation.lean#L54-L55

import Mathlib
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaTen
import Definitions.Def_RequestProject_EnvyRelaxation
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.RelaxEx

theorem FairSelling.RelaxEx.vbarSum_singleton (i : Fin 2) : vbarSum (v i) p {0} = 1 := by sorry

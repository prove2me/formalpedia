-- Prove2me | Theorems.Thm_FairSelling_RelaxEx_o_not_SEFXlit
-- name    : FairSelling.RelaxEx.o_not_SEFXlit
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:15:14.454979+00:00
-- url     : https://prove2.me/theorems/32ad6c57-1bd2-4881-a005-1b33125b09d4
-- title:
--   Relax Ex: o not SEFXlit
-- statement:
--   The same allocation does not satisfy the literal transcription of Definition 4.2 either.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EnvyRelaxation.lean#L96-L104
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EnvyRelaxation.lean#L96-L104

import Mathlib
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaTen
import Definitions.Def_RequestProject_EnvyRelaxation
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.RelaxEx

theorem FairSelling.RelaxEx.o_not_SEFXlit : ¬ SEFXlit v p o := by sorry

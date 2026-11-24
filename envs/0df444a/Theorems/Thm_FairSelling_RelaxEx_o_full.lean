-- Prove2me | Theorems.Thm_FairSelling_RelaxEx_o_full
-- name    : FairSelling.RelaxEx.o_full
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:15:11.536378+00:00
-- url     : https://prove2.me/theorems/13b6ffa6-3bb5-493b-8032-8319709ede09
-- title:
--   Relax Ex: o full
-- statement:
--   The outcome is a full allocation: every good is sold or allocated, and the whole sale
--   proceeds are distributed.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EnvyRelaxation.lean#L59-L68
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EnvyRelaxation.lean#L59-L68

import Mathlib
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaTen
import Definitions.Def_RequestProject_EnvyRelaxation
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.RelaxEx

theorem FairSelling.RelaxEx.o_full : o.Full p Finset.univ := by sorry

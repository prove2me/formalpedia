-- Prove2me | Theorems.Thm_FairSelling_RelaxEx_o_not_SEF1lit
-- name    : FairSelling.RelaxEx.o_not_SEF1lit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:15:05.16908+00:00
-- url     : https://prove2.me/theorems/a61ddffe-c94e-4256-aac2-9240b6198de4
-- title:
--   Relax Ex: o not SEF1lit
-- statement:
--   Yet it does **not** satisfy the literal transcription of Definition 4.1: agent `1` holds no
--   money, and the literal condition omits agent `0`'s money from the left-hand side.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EnvyRelaxation.lean#L81-L93
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EnvyRelaxation.lean#L81-L93

import Mathlib
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaTen
import Definitions.Def_RequestProject_EnvyRelaxation
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.RelaxEx

theorem FairSelling.RelaxEx.o_not_SEF1lit : ¬ SEF1lit v p o := by sorry

-- Prove2me | Theorems.Thm_FairChores_NineteenEighteenths_lamOf_key
-- name    : FairChores.NineteenEighteenths.lamOf_key
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:23:03.614315+00:00
-- url     : https://prove2.me/theorems/a1d32e76-8385-4755-8d48-0ef55fc7f5f9
-- title:
--   Nineteen Eighteenths: lam Of key
-- statement:
--   The Nineteen Eighteenths construction uses the lam Of key property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/NineteenEighteenths.lean#L224-L233
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/NineteenEighteenths.lean#L224-L233

import Mathlib
import Definitions.Def_RequestProject_ChoresExamples
import Definitions.Def_RequestProject_ChoresMMSPartition
import Definitions.Def_RequestProject_FeigeNorkinChores
import Definitions.Def_RequestProject_NineteenEighteenths
set_option autoImplicit true
open scoped BigOperators
open FairChores
open FairChores.NineteenEighteenths
open FeigeNorkinChores

theorem FairChores.NineteenEighteenths.lamOf_key {rho : ℝ} (hrho : rho < 19/18) : 720 * rho < lamOf rho * (380 - 360 * rho) := by sorry

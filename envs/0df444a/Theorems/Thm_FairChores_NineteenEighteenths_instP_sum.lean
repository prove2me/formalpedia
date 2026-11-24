-- Prove2me | Theorems.Thm_FairChores_NineteenEighteenths_instP_sum
-- name    : FairChores.NineteenEighteenths.instP_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:22:26.463664+00:00
-- url     : https://prove2.me/theorems/8ba11985-4a32-4f95-97d8-4a87def440d7
-- title:
--   Nineteen Eighteenths: inst P sum
-- statement:
--   The Nineteen Eighteenths construction uses the inst P sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/NineteenEighteenths.lean#L73-L77
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/NineteenEighteenths.lean#L73-L77

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

theorem FairChores.NineteenEighteenths.instP_sum (lam : ℝ) : (∑ t, instP lam t) = 1080 * lam := by sorry

-- Prove2me | Theorems.Thm_FairChores_NineteenEighteenths_instC_nonneg
-- name    : FairChores.NineteenEighteenths.instC_nonneg
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:29:44.271978+00:00
-- url     : https://prove2.me/theorems/ff59ae78-c599-4b48-947a-a94a290a7902
-- title:
--   Nineteen Eighteenths: inst C nonneg
-- statement:
--   The Nineteen Eighteenths construction uses the inst C nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/NineteenEighteenths.lean#L63-L71
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/NineteenEighteenths.lean#L63-L71

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

theorem FairChores.NineteenEighteenths.instC_nonneg {lam : ℝ} (hlam : 0 ≤ lam) : ∀ i t, 0 ≤ instC lam i t := by sorry

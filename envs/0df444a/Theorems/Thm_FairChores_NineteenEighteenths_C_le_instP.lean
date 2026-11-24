-- Prove2me | Theorems.Thm_FairChores_NineteenEighteenths_C_le_instP
-- name    : FairChores.NineteenEighteenths.C_le_instP
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:22:35.246814+00:00
-- url     : https://prove2.me/theorems/341ec42b-4df9-4744-bdad-82bec49495c5
-- title:
--   Nineteen Eighteenths: C le inst P
-- statement:
--   For `λ ≥ 2`, the outsourcing price dominates agent `1`'s cost chore by chore.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/NineteenEighteenths.lean#L89-L95
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/NineteenEighteenths.lean#L89-L95

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

theorem FairChores.NineteenEighteenths.C_le_instP {lam : ℝ} (hlam : 2 ≤ lam) (t : Fin 8) : (fcC t : ℝ) ≤ instP lam t := by sorry

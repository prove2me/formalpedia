-- Prove2me | Theorems.Thm_FairChores_NineteenEighteenths_R_le_instP
-- name    : FairChores.NineteenEighteenths.R_le_instP
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:22:29.803982+00:00
-- url     : https://prove2.me/theorems/55995aaa-44ec-4fb9-93e6-b4f3cb08000d
-- title:
--   Nineteen Eighteenths: R le inst P
-- statement:
--   For `λ ≥ 2`, the outsourcing price dominates agent `0`'s cost chore by chore.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/NineteenEighteenths.lean#L80-L86
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/NineteenEighteenths.lean#L80-L86

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

theorem FairChores.NineteenEighteenths.R_le_instP {lam : ℝ} (hlam : 2 ≤ lam) (t : Fin 8) : (fcR t : ℝ) ≤ instP lam t := by sorry

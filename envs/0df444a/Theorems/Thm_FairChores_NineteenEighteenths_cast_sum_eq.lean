-- Prove2me | Theorems.Thm_FairChores_NineteenEighteenths_cast_sum_eq
-- name    : FairChores.NineteenEighteenths.cast_sum_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:36:08.06627+00:00
-- url     : https://prove2.me/theorems/5046d250-6116-45f0-91cd-803269db5df0
-- title:
--   Nineteen Eighteenths: cast sum eq
-- statement:
--   Casting a natural-number bundle cost to `ℝ`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/NineteenEighteenths.lean#L46-L48
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/NineteenEighteenths.lean#L46-L48

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

theorem FairChores.NineteenEighteenths.cast_sum_eq (s : Finset (Fin 8)) (w : Fin 8 → ℕ) (m : ℕ) (h : ∑ t ∈ s, w t = m) :
    ∑ t ∈ s, (w t : ℝ) = m := by sorry

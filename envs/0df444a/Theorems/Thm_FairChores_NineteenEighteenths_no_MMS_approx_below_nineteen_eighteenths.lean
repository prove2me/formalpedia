-- Prove2me | Theorems.Thm_FairChores_NineteenEighteenths_no_MMS_approx_below_nineteen_eighteenths
-- name    : FairChores.NineteenEighteenths.no_MMS_approx_below_nineteen_eighteenths
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:29:50.663702+00:00
-- url     : https://prove2.me/theorems/836701f2-261a-4b5d-9b04-3ca50b8dc7f3
-- title:
--   Nineteen Eighteenths: no MMS approx below nineteen eighteenths
-- statement:
--   **Theorem 5 (impossibility half), in the manuscript's `ε`-form.**  For every `ε > 0`
--   there is an allocation instance with chores and optional outsourcing that has no
--   `(19/18 − ε)`-MMS allocation.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/NineteenEighteenths.lean#L351-L356
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/NineteenEighteenths.lean#L351-L356

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

theorem FairChores.NineteenEighteenths.no_MMS_approx_below_nineteen_eighteenths {eps : ℝ} (heps : 0 < eps) :
    ∃ (c : Fin 3 → Fin 8 → ℝ) (p : Fin 8 → ℝ),
      (∀ i t, 0 ≤ c i t) ∧ (∀ t, 0 ≤ p t) ∧
      ∀ o : Outcome (Fin 8) 3, o.Valid p →
        ∃ i, (19/18 - eps) * MMS 3 (c i) p < cost (c i) o i := by sorry

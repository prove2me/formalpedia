-- Prove2me | Theorems.Thm_Automata_na_prod_fin_run
-- name    : Automata.na_prod_fin_run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:28:18.747264+00:00
-- url     : https://prove2.me/theorems/02691fb3-7fd3-43b3-9c0e-dfc3c29abf92
-- title:
--   Automata: na prod fin run
-- statement:
--   The Automata construction uses the na prod fin run property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Prod.lean#L32-L42
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Prod.lean#L32-L42

import Definitions.Def_AutomataTheory_Automata_Basic
import Definitions.Def_AutomataTheory_Automata_Prod
set_option autoImplicit true
open Function Set Filter Stream'
open Automata
variable {I A : Type}
variable {M : I → NA A}

theorem Automata.na_prod_fin_run {n : ℕ} {as : Stream' A} {ss : Stream' (NA.Prod M).State} :
    (NA.Prod M).FinRun n as ss ↔ ∀ i, (M i).FinRun n as (fun k ↦ ss k i) := by sorry

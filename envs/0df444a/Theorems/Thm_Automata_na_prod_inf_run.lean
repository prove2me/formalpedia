-- Prove2me | Theorems.Thm_Automata_na_prod_inf_run
-- name    : Automata.na_prod_inf_run
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T04:28:25.327796+00:00
-- url     : https://prove2.me/theorems/5d21f2be-4bc9-41dd-a3d2-0ac3432e819e
-- title:
--   Automata: na prod inf run
-- statement:
--   The Automata construction uses the na prod inf run property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Prod.lean#L44-L54
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Prod.lean#L44-L54

import Definitions.Def_AutomataTheory_Automata_Basic
import Definitions.Def_AutomataTheory_Automata_Prod
set_option autoImplicit true
open Function Set Filter Stream'
open Automata
variable {I A : Type}
variable {M : I → NA A}

theorem Automata.na_prod_inf_run {as : Stream' A} {ss : Stream' (NA.Prod M).State} :
    (NA.Prod M).InfRun as ss ↔ ∀ i, (M i).InfRun as (fun k ↦ ss k i) := by sorry

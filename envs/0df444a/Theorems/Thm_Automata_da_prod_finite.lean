-- Prove2me | Theorems.Thm_Automata_da_prod_finite
-- name    : Automata.da_prod_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:19:56.002389+00:00
-- url     : https://prove2.me/theorems/2b88d53e-f075-456f-af9a-bf10cdd2f5e7
-- title:
--   Automata: da prod finite
-- statement:
--   The Automata construction uses the da prod finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/DetProd.lean#L40-L42
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/DetProd.lean#L40-L42

import Definitions.Def_AutomataTheory_Automata_Det
import Definitions.Def_AutomataTheory_Automata_DetProd
set_option autoImplicit true
open Function Set Filter Stream'
open Automata
variable {I A : Type}
variable (M : I → DA A)
variable [Finite I] [∀ i, Finite (M i).State]

theorem Automata.da_prod_finite :
    Finite (DA.Prod M).State := by sorry

-- Prove2me | Theorems.Thm_Automata_da_prod_inf_run
-- name    : Automata.da_prod_inf_run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:20:01.162616+00:00
-- url     : https://prove2.me/theorems/502a5bfd-73ed-487e-9e90-9d189761bcef
-- title:
--   Automata: da prod inf run
-- statement:
--   The Automata construction uses the da prod inf run property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/DetProd.lean#L31-L36
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/DetProd.lean#L31-L36

import Definitions.Def_AutomataTheory_Automata_Det
import Definitions.Def_AutomataTheory_Automata_DetProd
set_option autoImplicit true
open Function Set Filter Stream'
open Automata
variable {I A : Type}
variable (M : I → DA A)

theorem Automata.da_prod_inf_run (as : Stream' A) (i : I) :
    (· i) ∘ (DA.Prod M).DetRun as = (M i).DetRun as := by sorry

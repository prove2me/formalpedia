-- Prove2me | Theorems.Thm_Automata_da_prod_inf_occ
-- name    : Automata.da_prod_inf_occ
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T04:20:16.225308+00:00
-- url     : https://prove2.me/theorems/e57addd3-2862-4f0e-9bb1-0b8d5d743d1b
-- title:
--   Automata: da prod inf occ
-- statement:
--   The Automata construction uses the da prod inf occ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/DetProd.lean#L44-L47
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/DetProd.lean#L44-L47

import Definitions.Def_AutomataTheory_Automata_Det
import Definitions.Def_AutomataTheory_Automata_DetProd
set_option autoImplicit true
open Function Set Filter Stream'
open Automata
variable {I A : Type}
variable (M : I → DA A)
variable [Finite I] [∀ i, Finite (M i).State]

theorem Automata.da_prod_inf_occ (as : Stream' A) (i : I) :
    (· i) '' (InfOcc ((DA.Prod M).DetRun as)) =
    InfOcc ((· i) ∘ (DA.Prod M).DetRun as) := by sorry

-- Prove2me | Theorems.Thm_Automata_omega_reg_lang_finite_union_form
-- name    : Automata.omega_reg_lang_finite_union_form
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:31:39.327707+00:00
-- url     : https://prove2.me/theorems/851b8f9c-40e2-41c7-89bf-ff5aab4fd5d4
-- title:
--   Automata: omega reg lang finite union form
-- statement:
--   The ω-regular language accepted by a finite-state NA `M` is the union of ω-languages
--   of the form `(M.PairLang s0 sa) * (M.PairLang sa sa)^ω`, where `s0` and `sa` range over initial
--   and accepting states respectively.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Pair.lean#L343-L430
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Pair.lean#L343-L430

import Definitions.Def_AutomataTheory_Automata_Hist
import Definitions.Def_AutomataTheory_Languages_RegLang
import Definitions.Def_AutomataTheory_Sequences_InfOcc
import Definitions.Def_AutomataTheory_Automata_Pair
set_option autoImplicit true
open Function Set Filter Stream'
attribute [local implicit_reducible] Stream'
open Automata
attribute [local instance_reducible] NA.addHist
variable {A : Type}
variable {M : NA A} {acc : Set M.State}
attribute [local instance_reducible] NA.SingleInit

theorem Automata.omega_reg_lang_finite_union_form [h_fin : Finite M.State] :
    M.AcceptedOmegaLang acc = ⋃ s0 ∈ M.init, ⋃ sa ∈ acc, (M.PairLang s0 sa) * (M.PairLang sa sa)^ω := by sorry

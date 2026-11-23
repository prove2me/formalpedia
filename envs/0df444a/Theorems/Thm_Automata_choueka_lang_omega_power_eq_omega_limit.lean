-- Prove2me | Theorems.Thm_Automata_choueka_lang_omega_power_eq_omega_limit
-- name    : Automata.choueka_lang_omega_power_eq_omega_limit
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T04:31:44.985038+00:00
-- url     : https://prove2.me/theorems/029da5b1-b9f6-44cf-977c-9eea43337c76
-- title:
--   Automata: choueka lang omega power eq omega limit
-- statement:
--   If the language accepted by `M` is of the form `V∗`, then `V^ω = V∗ * (M.ChouekaLang acc)↗ω`.
--   Note that this theorem does need to assume that `M` is finite-state.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/ChouekaLemma.lean#L221-L232
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/ChouekaLemma.lean#L221-L232

import Definitions.Def_AutomataTheory_Languages_RegLang
import Definitions.Def_AutomataTheory_Mathlib_InfGraphRamsey
import Definitions.Def_AutomataTheory_Languages_ChouekaLemma
set_option autoImplicit true
open Function Set Filter Stream'
open scoped Computability
open Classical
attribute [local implicit_reducible] Stream'
open Automata
attribute [local instance_reducible] DA.toNA
variable {A : Type}

theorem Automata.choueka_lang_omega_power_eq_omega_limit [Inhabited A]
    {M : DA A} [Finite M.State] {acc : Set M.State}
    {V : Set (List A)} (h_lang : M.toNA.AcceptedLang acc = V∗) :
    V^ω = V∗ * (M.ChouekaLang acc)↗ω := by sorry

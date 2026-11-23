-- Prove2me | Theorems.Thm_Automata_choueka_lang_omega_power_subset_omega_limit
-- name    : Automata.choueka_lang_omega_power_subset_omega_limit
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T04:31:40.554366+00:00
-- url     : https://prove2.me/theorems/81bf97db-80d5-4421-9873-8fedd90b3260
-- title:
--   Automata: choueka lang omega power subset omega limit
-- statement:
--   If the language accepted by `M` is of the form `V∗`, then `V^ω ⊆ V∗ * (M.ChouekaLang acc)↗ω`.
--   Note that this theorem does need to assume that `M` is finite-state.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/ChouekaLemma.lean#L154-L216
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/ChouekaLemma.lean#L154-L216

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

theorem Automata.choueka_lang_omega_power_subset_omega_limit [Inhabited A]
    {M : DA A} [Finite M.State] {acc : Set M.State}
    {V : Set (List A)} (h_lang : M.toNA.AcceptedLang acc = V∗) :
    V^ω ⊆ V∗ * (M.ChouekaLang acc)↗ω := by sorry

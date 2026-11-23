-- Prove2me | Theorems.Thm_Automata_choueka_lang_omega_limit_subset_omega_power
-- name    : Automata.choueka_lang_omega_limit_subset_omega_power
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:31:24.543814+00:00
-- url     : https://prove2.me/theorems/7024725a-bf4b-474d-9442-778378ac8827
-- title:
--   Automata: choueka lang omega limit subset omega power
-- statement:
--   The ω-limit of the Choueka language of `M` is a subset of the ω-power of the language of `M`.
--   Note that this theorem does not need to assume that `M` is finite-state.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/ChouekaLemma.lean#L61-L107
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/ChouekaLemma.lean#L61-L107

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

theorem Automata.choueka_lang_omega_limit_subset_omega_power [Inhabited A] {M : DA A} {acc : Set M.State} :
    (M.ChouekaLang acc)↗ω ⊆ (M.toNA.AcceptedLang acc)^ω := by sorry

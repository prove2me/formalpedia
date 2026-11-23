-- Prove2me | Theorems.Thm_Automata_pair_acc_lang_frequently_from_run
-- name    : Automata.pair_acc_lang_frequently_from_run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:31:19.785204+00:00
-- url     : https://prove2.me/theorems/119b4d57-2a01-4642-9da2-259c51afff12
-- title:
--   Automata: pair acc lang frequently from run
-- statement:
--   If accepting states appear infinitely often in a run and φ : Stream' ℕ is StrictMono,
--   then there exist infinitely many `m` such that the segment of the run from `φ(m)` to `φ(m + 1)`
--   contains at least one accepting state.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Pair.lean#L151-L172
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Pair.lean#L151-L172

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

theorem Automata.pair_acc_lang_frequently_from_run {as : Stream' A} {ss : Stream' M.State} {φ : Stream' ℕ}
    (h_next : ∀ k, ss (k + 1) ∈ M.next (ss k) (as k)) (h_acc : ∃ᶠ k in Filter.atTop, ss k ∈ acc) (h_mono : StrictMono φ) :
    ∃ᶠ m in Filter.atTop, as.extract (φ m) (φ (m + 1)) ∈ M.PairAccLang acc (ss (φ m)) (ss (φ (m + 1))) := by sorry

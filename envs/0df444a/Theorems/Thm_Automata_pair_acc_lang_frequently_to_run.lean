-- Prove2me | Theorems.Thm_Automata_pair_acc_lang_frequently_to_run
-- name    : Automata.pair_acc_lang_frequently_to_run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:31:22.406413+00:00
-- url     : https://prove2.me/theorems/c52a2dec-bf1d-41bf-b0f8-600e5622faa9
-- title:
--   Automata: pair acc lang frequently to run
-- statement:
--   The following result is technical and used to prove the saturation property of
--   the Buchi congruence.  Its main purpose is to "fill in" the states between the
--   successive `ss' m` to produce a well-formed run in which the accepting states appear
--   infinitely often.  Note that `ss` needs to agree with `ss'` only at positions `φ m`:
--   `∀ m, ss (φ m) = ss' m`.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Pair.lean#L180-L243
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Pair.lean#L180-L243

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

theorem Automata.pair_acc_lang_frequently_to_run {φ : Stream' ℕ} {as : Stream' A} (ss' : Stream' M.State)
    (h_mono : StrictMono φ) (h_zero : φ 0 = 0)
    (h_pair : ∀ m, as.extract (φ m) (φ (m + 1)) ∈ M.PairLang (ss' m) (ss' (m + 1)))
    (h_inf : ∃ᶠ m in atTop, as.extract (φ m) (φ (m + 1)) ∈ M.PairAccLang acc (ss' m) (ss' (m + 1))) :
    ∃ ss : Stream' M.State, (∀ m, ss (φ m) = ss' m) ∧
      (∀ k, ss (k + 1) ∈ M.next (ss k) (as (k))) ∧ (∃ᶠ k in atTop, ss k ∈ acc) := by sorry

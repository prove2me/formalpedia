-- Prove2me | Theorems.Thm_Automata_pair_lang_fin_subseq
-- name    : Automata.pair_lang_fin_subseq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:30:44.782485+00:00
-- url     : https://prove2.me/theorems/1fa56a22-036f-4e06-88a6-d39e88c3aba7
-- title:
--   Automata: pair lang fin subseq
-- statement:
--   The following intuitive obvious results are needed to prove that
--   Buchi congruence is indeed a right congruence.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Pair.lean#L58-L63
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Pair.lean#L58-L63

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

theorem Automata.pair_lang_fin_subseq {as : Stream' A} {ss : Stream' M.State} {m n : ℕ}
    (h_next : ∀ k, ss (k + 1) ∈ M.next (ss k) (as k)) (h_m_n : m ≤ n) :
    as.extract m n ∈ M.PairLang (ss m) (ss n) := by sorry

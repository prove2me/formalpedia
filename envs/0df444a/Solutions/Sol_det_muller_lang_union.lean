-- Prove2me | solution 1 for det_muller_lang_union
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:51:58.972154+00:00
-- url     : https://prove2.me/submissions/71875dfc-816a-4b26-8a24-426d39a51071

import Definitions.Def_AutomataTheory_Automata_DetConcat
import Definitions.Def_AutomataTheory_Automata_DetProd
import Definitions.Def_AutomataTheory_Languages_OmegaRegLang
import Definitions.Def_AutomataTheory_Languages_DetMullerLang
import Theorems.Thm_Automata_da_prod_finite
import Theorems.Thm_Automata_det_muller_accept_union


set_option autoImplicit true
open Function Set Stream'
open scoped Computability
attribute [local implicit_reducible] Stream'
attribute [local instance_reducible] Automata.DA.toNA Automata.DA.Prod
variable {A : Type}
theorem _root_.solution {L0 L1 : Set (Stream' A)}
    (h0 : DetMullerLang L0) (h1 : DetMullerLang L1) : DetMullerLang (L0 ∪ L1) := by
  obtain ⟨M0, accSet0, h_fin0, rfl⟩ := h0
  obtain ⟨M1, accSet1, h_fin1, rfl⟩ := h1
  let M : Fin 2 → Automata.DA A
    | 0 => M0
    | 1 => M1
  let accSet : (i : Fin 2) → Set (Set (M i).State)
    | 0 => accSet0
    | 1 => accSet1
  use (Automata.DA.Prod M), (Automata.DA.MullerAcc_Union M accSet)
  have : ∀ i, Finite (M i).State := by simp +instances [Fin.forall_fin_two, M, h_fin0, h_fin1]
  constructor
  · exact Automata.da_prod_finite M
  · ext as
    simp +instances [Automata.det_muller_accept_union M accSet as, Fin.exists_fin_two] ; grind

-- Prove2me | Theorems.Thm_DeciSigma1_Automata_upperRun_snoc
-- name    : DeciSigma1.Automata.upperRun_snoc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:19:43.122793+00:00
-- url     : https://prove2.me/theorems/c224c0d7-7e0b-495b-9691-8e32f845f562
-- title:
--   Automata: upper Run snoc
-- statement:
--   The Automata construction uses the upper Run snoc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Automata/Constraints.lean#L209-L211
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Automata/Constraints.lean#L209-L211

module
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Closure
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Constraints
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1
open DeciSigma1.Constraints
open DeciSigma1.Automata
variable {n : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

theorem DeciSigma1.Automata.upperRun_snoc (Γ : List (LitT n V)) (x : V) (w : List (Fin n)) (c : Fin n) :
    upperRun Γ x (w ++ [c]) = upperStep Γ (upperRun Γ x w) c := by sorry

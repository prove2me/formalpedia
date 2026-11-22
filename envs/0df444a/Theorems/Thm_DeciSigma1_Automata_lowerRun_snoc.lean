-- Prove2me | Theorems.Thm_DeciSigma1_Automata_lowerRun_snoc
-- name    : DeciSigma1.Automata.lowerRun_snoc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:20:02.05985+00:00
-- url     : https://prove2.me/theorems/c4529b17-2ccf-4284-a5e0-dce1768b58a2
-- title:
--   Automata: lower Run snoc
-- statement:
--   The Automata construction uses the lower Run snoc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Automata/Constraints.lean#L212-L214
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Automata/Constraints.lean#L212-L214

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

theorem DeciSigma1.Automata.lowerRun_snoc (Γ : List (LitT n V)) (x : V) (w : List (Fin n)) (c : Fin n) :
    lowerRun Γ x (w ++ [c]) = lowerStep Γ (lowerRun Γ x w) c := by sorry

-- Prove2me | Theorems.Thm_DeciSigma1_Automata_upperStep_empty
-- name    : DeciSigma1.Automata.upperStep_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:19:59.129792+00:00
-- url     : https://prove2.me/theorems/d8cfa9ac-25fd-4661-a943-12790ff35c84
-- title:
--   Automata: upper Step empty
-- statement:
--   The Automata construction uses the upper Step empty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Automata/Constraints.lean#L216-L217
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Automata/Constraints.lean#L216-L217

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

theorem DeciSigma1.Automata.upperStep_empty (Γ : List (LitT n V)) (c : Fin n) :
    upperStep Γ ∅ c = ∅ := by sorry

-- Prove2me | Theorems.Thm_DeciSigma1_Automata_lowerRun_pop
-- name    : DeciSigma1.Automata.lowerRun_pop
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:28:22.273301+00:00
-- url     : https://prove2.me/theorems/fa1915a9-2c94-4240-a3e4-d2cdbef0ec94
-- title:
--   Automata: lower Run pop
-- statement:
--   The Automata construction uses the lower Run pop property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Automata/Constraints.lean#L294-L306
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Automata/Constraints.lean#L294-L306

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

theorem DeciSigma1.Automata.lowerRun_pop {Γ : List (LitT n V)} {bs : Fin n → V} {y a : V} {w : List (Fin n)} (c : Fin n)
    (hu : LitT.leF y bs ∈ Γ) (h : a ∈ lowerRun Γ y (c :: w)) :
    a ∈ lowerRun Γ (bs c) w := by sorry

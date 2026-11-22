-- Prove2me | Theorems.Thm_DeciSigma1_Automata_normal_moves
-- name    : DeciSigma1.Automata.normal_moves
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:28:28.701853+00:00
-- url     : https://prove2.me/theorems/efb4b0ea-c6be-4363-8e9c-88f6ddee2709
-- title:
--   Automata: normal moves
-- statement:
--   The Automata construction uses the normal moves property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Automata/Constraints.lean#L342-L345
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Automata/Constraints.lean#L342-L345

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

theorem DeciSigma1.Automata.normal_moves {Γ : List (LitT n V)} {x y : V} {u t : List (Fin n)}
    (h : Normal Γ x u y t) : Moves Γ (x, u) (y, t) := by sorry

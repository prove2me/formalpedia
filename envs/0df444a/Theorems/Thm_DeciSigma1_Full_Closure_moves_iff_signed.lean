-- Prove2me | Theorems.Thm_DeciSigma1_Full_Closure_moves_iff_signed
-- name    : DeciSigma1.Full.Closure.moves_iff_signed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:06:12.575697+00:00
-- url     : https://prove2.me/theorems/bf6f5215-87c8-4062-97e0-c9cc87cd50bc
-- title:
--   Closure: moves iff signed
-- statement:
--   Move derivations are the move derivations of the signed translation.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Automata.lean#L113-L122
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Automata.lean#L113-L122

module
public import Mathlib.Data.Fintype.Powerset
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Constraints
public import Definitions.Def_LeanPool_DeciSigma1_Full_Closure_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Decide
public import Definitions.Def_LeanPool_DeciSigma1_Full_Closure_Automata
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Closure
open DeciSigma1.Semantics DeciSigma1.Constraints
variable {n : ℕ} {V : Type*}
variable {c : Fin n → Bool} {Γ : List (LitT n V)}

theorem DeciSigma1.Full.Closure.moves_iff_signed {p q : Config n V} :
    Relation.ReflTransGen (Move c Γ) p q ↔
      Automata.Moves (signed c Γ) (assoc p) (assoc q) := by sorry

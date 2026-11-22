-- Prove2me | Theorems.Thm_DeciSigma1_Full_Closure_move_sign
-- name    : DeciSigma1.Full.Closure.move_sign
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:08:22.389009+00:00
-- url     : https://prove2.me/theorems/238aa122-bf5b-4b21-9f6c-d378cb8060c3
-- title:
--   Closure: move sign
-- statement:
--   A move preserves the sign of a configuration shifted by the polarity of its path.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Automata.lean#L131-L134
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Automata.lean#L131-L134

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

theorem DeciSigma1.Full.Closure.move_sign {p q : Config n V} (h : Move c Γ p q) :
    Bool.xor q.2.1 (polarity c q.2.2) =
      Bool.xor p.2.1 (polarity c p.2.2) := by sorry

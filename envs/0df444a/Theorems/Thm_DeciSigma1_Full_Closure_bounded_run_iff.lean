-- Prove2me | Theorems.Thm_DeciSigma1_Full_Closure_bounded_run_iff
-- name    : DeciSigma1.Full.Closure.bounded_run_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:09:14.943555+00:00
-- url     : https://prove2.me/theorems/d6ab561c-6b11-43e5-8e87-15e41bf65175
-- title:
--   Closure: bounded run iff
-- statement:
--   A state reachable by some word is reachable by a word of length at most the number of states.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Automata.lean#L269-L278
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Automata.lean#L269-L278

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
open DeciSigma1.Automata
open DeciSigma1.Constraints
variable {n : ℕ} {V : Type*}

theorem DeciSigma1.Full.Closure.bounded_run_iff {S : Type*} [Fintype S] (M : Semiautomaton (Fin n) S)
    (q : S) (H : S → Prop) :
    (∃ w ∈ wordsUpTo (α := Fin n) (Fintype.card S), H (runFrom M.step q w)) ↔
      ∃ w, H (runFrom M.step q w) := by sorry

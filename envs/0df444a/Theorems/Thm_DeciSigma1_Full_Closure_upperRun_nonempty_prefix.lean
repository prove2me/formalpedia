-- Prove2me | Theorems.Thm_DeciSigma1_Full_Closure_upperRun_nonempty_prefix
-- name    : DeciSigma1.Full.Closure.upperRun_nonempty_prefix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:09:42.442701+00:00
-- url     : https://prove2.me/theorems/509dcbbf-848b-43ea-bf4d-f0701a14b224
-- title:
--   Closure: upper Run nonempty prefix
-- statement:
--   If the upper run on `v` is nonempty, so is the upper run on every prefix of `v`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Automata.lean#L389-L395
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Automata.lean#L389-L395

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
variable [Fintype V] [DecidableEq V]
variable (c : Fin n → Bool) (Γ : List (LitT n V))
variable {c Γ}
variable (c Γ)
variable {c Γ}

theorem DeciSigma1.Full.Closure.upperRun_nonempty_prefix {p : V × Bool} {u v : List (Fin n)}
    (hp : u.IsPrefix v) (h : (Automata.upperRun (signed c Γ) p v).Nonempty) :
    (Automata.upperRun (signed c Γ) p u).Nonempty := by sorry

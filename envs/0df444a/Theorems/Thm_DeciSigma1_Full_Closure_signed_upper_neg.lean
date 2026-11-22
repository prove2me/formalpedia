-- Prove2me | Theorems.Thm_DeciSigma1_Full_Closure_signed_upper_neg
-- name    : DeciSigma1.Full.Closure.signed_upper_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:06:45.102739+00:00
-- url     : https://prove2.me/theorems/08596e8e-e9e7-4ba7-ab9f-b4bbd5e8b5cb
-- title:
--   Closure: signed upper neg
-- statement:
--   The bounded variable of an upper constructor bound of the signed translation is the root of a
--   negative fact.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Automata.lean#L171-L178
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Automata.lean#L171-L178

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
variable [Fintype V] [DecidableEq V]
omit [Fintype V] [DecidableEq V]

theorem DeciSigma1.Full.Closure.signed_upper_neg {r : V × Bool} {a : Fin n → V × Bool}
    (h : LitT.leF r a ∈ signed c Γ) : Neg Γ (r.1, r.2, []) := by sorry

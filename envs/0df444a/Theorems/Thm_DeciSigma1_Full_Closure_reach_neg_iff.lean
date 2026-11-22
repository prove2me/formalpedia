-- Prove2me | Theorems.Thm_DeciSigma1_Full_Closure_reach_neg_iff
-- name    : DeciSigma1.Full.Closure.reach_neg_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:09:33.661998+00:00
-- url     : https://prove2.me/theorems/01a4d5c8-6df5-4a13-96bf-ae904fdf7f70
-- title:
--   Closure: reach neg iff
-- statement:
--   The Closure construction uses the reach neg iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Automata.lean#L333-L350
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Automata.lean#L333-L350

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

theorem DeciSigma1.Full.Closure.reach_neg_iff {p : V} {s : Bool} {u : List (Fin n)} :
    (∃ n, Neg Γ n ∧ Reach c Γ (p, s, u) n) ↔
      ∃ z, (Automata.upperRun (signed c Γ) (p,
          s) (u ++ z) ∩ forbiddenPredecessors c Γ).Nonempty := by sorry

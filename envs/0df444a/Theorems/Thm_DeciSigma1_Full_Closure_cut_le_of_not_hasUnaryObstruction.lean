-- Prove2me | Theorems.Thm_DeciSigma1_Full_Closure_cut_le_of_not_hasUnaryObstruction
-- name    : DeciSigma1.Full.Closure.cut_le_of_not_hasUnaryObstruction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:06:14.826398+00:00
-- url     : https://prove2.me/theorems/15e4e458-564b-40ad-ab91-9838e8e161a1
-- title:
--   Closure: cut le of not has Unary Obstruction
-- statement:
--   Without a unary obstruction at `(p, u)`, a nonempty upper run along `u ++ α` ends within `u`:
--   the cut `i` is at most `|u|`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Automata.lean#L411-L421
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Automata.lean#L411-L421

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

theorem DeciSigma1.Full.Closure.cut_le_of_not_hasUnaryObstruction {p : V × Bool} {u α : List (Fin n)} {i : ℕ}
    (hdead : ¬ HasUnaryObstruction c Γ p u) (hi : i ≤ (u ++ α).length)
    (hp : (Automata.upperRun (signed c Γ) p ((u ++ α).take i)).Nonempty) :
    i ≤ u.length := by sorry

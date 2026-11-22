-- Prove2me | Theorems.Thm_DeciSigma1_Full_Closure_self_guard_ne
-- name    : DeciSigma1.Full.Closure.self_guard_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:07:17.435776+00:00
-- url     : https://prove2.me/theorems/394ab36b-dd73-4e88-beaa-9754c33f77a5
-- title:
--   Closure: self guard ne
-- statement:
--   The Closure construction uses the self guard ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Automata.lean#L467-L477
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Automata.lean#L467-L477

module
public import Mathlib.Data.Fintype.Powerset
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Constraints
public import Definitions.Def_LeanPool_DeciSigma1_Full_Closure_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Decide
public import Definitions.Def_LeanPool_DeciSigma1_Full_Closure_Automata
public import Theorems.Thm_DeciSigma1_Constraints_UpperAt_map

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

theorem DeciSigma1.Full.Closure.self_guard_ne {p : V × Bool} {u : List (Fin n)} {i j : ℕ}
    (hg : (Automata.upperRun (signed c Γ) p (u.take i) ∩
      (Automata.upperRun (signed c Γ) p (u.take j)).map flipEmb).Nonempty) : i ≠ j := by sorry

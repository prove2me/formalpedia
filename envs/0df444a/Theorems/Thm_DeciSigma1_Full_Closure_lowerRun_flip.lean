-- Prove2me | Theorems.Thm_DeciSigma1_Full_Closure_lowerRun_flip
-- name    : DeciSigma1.Full.Closure.lowerRun_flip
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:05:36.078679+00:00
-- url     : https://prove2.me/theorems/6771b4b9-b000-4924-a51f-786ed62ed3ec
-- title:
--   Closure: lower Run flip
-- statement:
--   Exchanging the signs turns the upper run of a signed variable into the lower run of its
--   opposite sign.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Automata.lean#L157-L166
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Automata.lean#L157-L166

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
open DeciSigma1.Semantics DeciSigma1.Constraints
variable {n : ℕ} {V : Type*}
variable {c : Fin n → Bool} {Γ : List (LitT n V)}
variable [Fintype V] [DecidableEq V]

theorem DeciSigma1.Full.Closure.lowerRun_flip (y : V × Bool) (w : List (Fin n)) :
    Automata.lowerRun (signed c Γ) (flipV y) w =
      (Automata.upperRun (signed c Γ) y w).map flipEmb := by sorry

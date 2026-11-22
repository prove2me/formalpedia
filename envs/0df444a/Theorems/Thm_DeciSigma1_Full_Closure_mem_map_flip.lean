-- Prove2me | Theorems.Thm_DeciSigma1_Full_Closure_mem_map_flip
-- name    : DeciSigma1.Full.Closure.mem_map_flip
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:05:57.920813+00:00
-- url     : https://prove2.me/theorems/84670b3b-450a-4f05-834a-7e21f6cf220e
-- title:
--   Closure: mem map flip
-- statement:
--   The Closure construction uses the mem map flip property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Automata.lean#L148-L153
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Automata.lean#L148-L153

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
omit [Fintype V] [DecidableEq V]

theorem DeciSigma1.Full.Closure.mem_map_flip {S : Finset (V × Bool)} {x : V × Bool} :
    x ∈ S.map flipEmb ↔ flipV x ∈ S := by sorry

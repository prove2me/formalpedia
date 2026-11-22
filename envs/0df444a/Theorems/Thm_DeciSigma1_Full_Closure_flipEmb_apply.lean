-- Prove2me | Theorems.Thm_DeciSigma1_Full_Closure_flipEmb_apply
-- name    : DeciSigma1.Full.Closure.flipEmb_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:05:26.997402+00:00
-- url     : https://prove2.me/theorems/ca53bd56-0b8f-4da7-bc11-a7c59a1b3969
-- title:
--   Closure: flip Emb apply
-- statement:
--   The Closure construction uses the flip Emb apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Automata.lean#L128-L128
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Automata.lean#L128-L128

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

theorem DeciSigma1.Full.Closure.flipEmb_apply (p : V × Bool) : flipEmb p = flipV p := by sorry

attribute [defeq] DeciSigma1.Full.Closure.flipEmb_apply

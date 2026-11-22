-- Prove2me | Theorems.Thm_DeciSigma1_Automata_lowerRun_push
-- name    : DeciSigma1.Automata.lowerRun_push
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:28:19.419011+00:00
-- url     : https://prove2.me/theorems/0c460025-d622-46c8-a6c7-aa825738909a
-- title:
--   Automata: lower Run push
-- statement:
--   The Automata construction uses the lower Run push property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Automata/Constraints.lean#L281-L292
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Automata/Constraints.lean#L281-L292

module
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Closure
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Constraints
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1
open DeciSigma1.Constraints
open DeciSigma1.Automata
variable {n : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

theorem DeciSigma1.Automata.lowerRun_push {Γ : List (LitT n V)} {as : Fin n → V} {y a : V} {w : List (Fin n)}
    (c : Fin n) (hl : LitT.fLe as y ∈ Γ) (h : a ∈ lowerRun Γ (as c) w) :
    a ∈ lowerRun Γ y (c :: w) := by sorry

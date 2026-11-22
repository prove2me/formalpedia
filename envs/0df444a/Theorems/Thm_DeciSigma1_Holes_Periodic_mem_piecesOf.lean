-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Periodic_mem_piecesOf
-- name    : DeciSigma1.Holes.Periodic.mem_piecesOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:45:49.9583+00:00
-- url     : https://prove2.me/theorems/42797ac4-b119-4916-a892-f4f32c8c954d
-- title:
--   Periodic: mem pieces Of
-- statement:
--   The Periodic construction uses the mem pieces Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Basic.lean#L218-L220
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Basic.lean#L218-L220

module
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Words_Periods
public import Mathlib.Order.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Basic
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Periodic
open DeciSigma1.Readers DeciSigma1.Words
variable {α : Type} {k : ℕ}
variable [DecidableEq α] (W : Fin k → List α) (d : ℕ)

theorem DeciSigma1.Holes.Periodic.mem_piecesOf {ρ : List α} {P : Piece W ρ.length} :
    P ∈ piecesOf W ρ ↔ IsConjugate P.root ρ := by sorry

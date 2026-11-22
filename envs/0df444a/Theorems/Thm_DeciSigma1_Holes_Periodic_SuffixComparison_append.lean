-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Periodic_SuffixComparison_append
-- name    : DeciSigma1.Holes.Periodic.SuffixComparison.append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:46:20.728668+00:00
-- url     : https://prove2.me/theorems/d05d1af0-311d-4013-b02b-cdaa68322be4
-- title:
--   Suffix Comparison: append
-- statement:
--   The Suffix Comparison construction uses the append property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Transport.lean#L87-L94
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Transport.lean#L87-L94

module
public import Mathlib.Tactic.Positivity.Basic
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Pieces
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Transport
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Periodic
open DeciSigma1.Readers DeciSigma1.Words
open DeciSigma1.Readers.Table
variable {α : Type} {k : ℕ}
open DeciSigma1.Holes.Periodic.SuffixComparison
variable {y z : List α} {b a : ℕ}

theorem DeciSigma1.Holes.Periodic.SuffixComparison.append {r : ℕ} (h₁ : ∀ n < r, y[b + n]? = z[a + n]?)
    (h₂ : SuffixComparison y (b + r) z (a + r)) :
    SuffixComparison y b z a := by sorry

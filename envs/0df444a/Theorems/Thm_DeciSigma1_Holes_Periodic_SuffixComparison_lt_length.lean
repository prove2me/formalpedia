-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Periodic_SuffixComparison_lt_length
-- name    : DeciSigma1.Holes.Periodic.SuffixComparison.lt_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:44:28.745585+00:00
-- url     : https://prove2.me/theorems/b38458c9-eb17-4998-bc8e-4e4f3b9dac8e
-- title:
--   Suffix Comparison: lt length
-- statement:
--   The Suffix Comparison construction uses the lt length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Transport.lean#L79-L85
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Transport.lean#L79-L85

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

theorem DeciSigma1.Holes.Periodic.SuffixComparison.lt_length (h : SuffixComparison y b z a) {n : ℕ} (hn : b + n < y.length) :
    a + n < z.length := by sorry

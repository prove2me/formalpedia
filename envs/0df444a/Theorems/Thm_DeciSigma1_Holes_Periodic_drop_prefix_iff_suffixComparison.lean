-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Periodic_drop_prefix_iff_suffixComparison
-- name    : DeciSigma1.Holes.Periodic.drop_prefix_iff_suffixComparison
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:42:55.874912+00:00
-- url     : https://prove2.me/theorems/357333ac-7a4c-4f4b-8212-f8cc619ac338
-- title:
--   Periodic: drop prefix iff suffix Comparison
-- statement:
--   The Periodic construction uses the drop prefix iff suffix Comparison property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Transport.lean#L58-L68
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Transport.lean#L58-L68

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

theorem DeciSigma1.Holes.Periodic.drop_prefix_iff_suffixComparison {y z : List α} {b a : ℕ} :
    y.drop b <+: z.drop a ↔ SuffixComparison y b z a := by sorry

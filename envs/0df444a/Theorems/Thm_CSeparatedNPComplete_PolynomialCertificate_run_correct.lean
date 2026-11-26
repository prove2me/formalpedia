-- Prove2me | Theorems.Thm_CSeparatedNPComplete_PolynomialCertificate_run_correct
-- name    : CSeparatedNPComplete.PolynomialCertificate.run_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:50:38.139993+00:00
-- url     : https://prove2.me/theorems/fb814a9f-cc22-4189-9bde-de78aa68ab99
-- title:
--   Polynomial Certificate: run correct
-- statement:
--   The Polynomial Certificate construction uses the run correct property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/PolynomialCertificate.lean#L93-L101
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/PolynomialCertificate.lean#L93-L101

module
public import Definitions.Def_CSeparatedNPComplete_PartitionEquivalence
public import Mathlib.Data.Nat.Size
public import Definitions.Def_CSeparatedNPComplete_PolynomialCertificate
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete CSeparatedNPComplete.PolynomialCertificate

theorem CSeparatedNPComplete.PolynomialCertificate.run_correct (xs : List (ℕ × Bool)) :
    (run xs).leftCount = leftCount xs ∧ (run xs).rightCount = rightCount xs ∧
    (run xs).leftSum = leftSum xs ∧ (run xs).rightSum = rightSum xs := by sorry

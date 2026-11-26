-- Prove2me | Theorems.Thm_CSeparatedNPComplete_PolynomialCertificate_counts_total
-- name    : CSeparatedNPComplete.PolynomialCertificate.counts_total
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:51:04.532046+00:00
-- url     : https://prove2.me/theorems/f505e81a-b04b-4767-96c5-bbb1d8f21f82
-- title:
--   Polynomial Certificate: counts total
-- statement:
--   The Polynomial Certificate construction uses the counts total property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/PolynomialCertificate.lean#L169-L174
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/PolynomialCertificate.lean#L169-L174

module
public import Definitions.Def_CSeparatedNPComplete_PartitionEquivalence
public import Mathlib.Data.Nat.Size
public import Definitions.Def_CSeparatedNPComplete_PolynomialCertificate
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete CSeparatedNPComplete.PolynomialCertificate

theorem CSeparatedNPComplete.PolynomialCertificate.counts_total (xs : List (ℕ × Bool)) : leftCount xs + rightCount xs = xs.length := by sorry

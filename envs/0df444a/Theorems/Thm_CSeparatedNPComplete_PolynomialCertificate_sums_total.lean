-- Prove2me | Theorems.Thm_CSeparatedNPComplete_PolynomialCertificate_sums_total
-- name    : CSeparatedNPComplete.PolynomialCertificate.sums_total
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:50:52.961425+00:00
-- url     : https://prove2.me/theorems/34efde0f-230d-4deb-a23a-cbf7c7b80a00
-- title:
--   Polynomial Certificate: sums total
-- statement:
--   The Polynomial Certificate construction uses the sums total property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/PolynomialCertificate.lean#L176-L181
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/PolynomialCertificate.lean#L176-L181

module
public import Definitions.Def_CSeparatedNPComplete_PartitionEquivalence
public import Mathlib.Data.Nat.Size
public import Definitions.Def_CSeparatedNPComplete_PolynomialCertificate
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete CSeparatedNPComplete.PolynomialCertificate

theorem CSeparatedNPComplete.PolynomialCertificate.sums_total (xs : List (ℕ × Bool)) : leftSum xs + rightSum xs = (xs.map Prod.fst).sum := by sorry

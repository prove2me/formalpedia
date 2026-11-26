-- Prove2me | Theorems.Thm_CSeparatedNPComplete_PolynomialCertificate_binary_has_certificate
-- name    : CSeparatedNPComplete.PolynomialCertificate.binary_has_certificate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:51:03.194312+00:00
-- url     : https://prove2.me/theorems/82c7a034-0551-4aae-9666-7fc6892432fe
-- title:
--   Polynomial Certificate: binary has certificate
-- statement:
--   The Polynomial Certificate construction uses the binary has certificate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/PolynomialCertificate.lean#L226-L231
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/PolynomialCertificate.lean#L226-L231

module
public import Definitions.Def_CSeparatedNPComplete_PartitionEquivalence
public import Mathlib.Data.Nat.Size
public import Definitions.Def_CSeparatedNPComplete_PolynomialCertificate
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete CSeparatedNPComplete.PolynomialCertificate

theorem CSeparatedNPComplete.PolynomialCertificate.binary_has_certificate {n : ℕ} (a : Vec n) (ha : is_binary a) :
    ∃ b : Fin n → Bool, selector b = a := by sorry

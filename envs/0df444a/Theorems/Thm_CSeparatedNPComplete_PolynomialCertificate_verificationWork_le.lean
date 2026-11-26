-- Prove2me | Theorems.Thm_CSeparatedNPComplete_PolynomialCertificate_verificationWork_le
-- name    : CSeparatedNPComplete.PolynomialCertificate.verificationWork_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:50:44.404995+00:00
-- url     : https://prove2.me/theorems/65a3f001-a17e-5b31-a691-bc03aacb8961
-- title:
--   Polynomial Certificate: verification Work le
-- statement:
--   The Polynomial Certificate construction uses the verification Work le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/PolynomialCertificate.lean#L147-L159
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/PolynomialCertificate.lean#L147-L159

module
public import Definitions.Def_CSeparatedNPComplete_PartitionEquivalence
public import Mathlib.Data.Nat.Size
public import Definitions.Def_CSeparatedNPComplete_PolynomialCertificate
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete CSeparatedNPComplete.PolynomialCertificate

theorem CSeparatedNPComplete.PolynomialCertificate.verificationWork_le {n : ℕ} (s : Fin n → ℕ) (b : Fin n → Bool) :
    verificationWork s b ≤ 128 * (inputBits s + 1) ^ 2 := by sorry

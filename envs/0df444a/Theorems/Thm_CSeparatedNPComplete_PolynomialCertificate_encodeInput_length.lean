-- Prove2me | Theorems.Thm_CSeparatedNPComplete_PolynomialCertificate_encodeInput_length
-- name    : CSeparatedNPComplete.PolynomialCertificate.encodeInput_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:56:27.592269+00:00
-- url     : https://prove2.me/theorems/14f47194-aea3-4f9d-8472-68fef27bfb32
-- title:
--   Polynomial Certificate: encode Input length
-- statement:
--   The Polynomial Certificate construction uses the encode Input length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/PolynomialCertificate.lean#L161-L167
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/PolynomialCertificate.lean#L161-L167

module
public import Definitions.Def_CSeparatedNPComplete_PartitionEquivalence
public import Mathlib.Data.Nat.Size
public import Definitions.Def_CSeparatedNPComplete_PolynomialCertificate
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete CSeparatedNPComplete.PolynomialCertificate

theorem CSeparatedNPComplete.PolynomialCertificate.encodeInput_length {n : ℕ} (s : Fin n → ℕ) :
    (encodeInput s).length = inputBits s := by sorry

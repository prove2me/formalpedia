-- Prove2me | Theorems.Thm_CSeparatedNPComplete_PolynomialCertificate_verify_iff_partition
-- name    : CSeparatedNPComplete.PolynomialCertificate.verify_iff_partition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:50:58.757801+00:00
-- url     : https://prove2.me/theorems/83bc505d-bf01-5872-b377-632d66202857
-- title:
--   Polynomial Certificate: verify iff partition
-- statement:
--   The Polynomial Certificate construction uses the verify iff partition property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/PolynomialCertificate.lean#L204-L224
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/PolynomialCertificate.lean#L204-L224

module
public import Definitions.Def_CSeparatedNPComplete_PartitionEquivalence
public import Mathlib.Data.Nat.Size
public import Definitions.Def_CSeparatedNPComplete_PolynomialCertificate
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete CSeparatedNPComplete.PolynomialCertificate

theorem CSeparatedNPComplete.PolynomialCertificate.verify_iff_partition {n : ℕ} (s : Fin n → ℕ) (b : Fin n → Bool) :
    verify s b = true ↔ is_ec_partition (selector b) (fun i => (s i : ℝ)) := by sorry

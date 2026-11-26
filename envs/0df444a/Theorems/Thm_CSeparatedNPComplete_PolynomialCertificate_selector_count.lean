-- Prove2me | Theorems.Thm_CSeparatedNPComplete_PolynomialCertificate_selector_count
-- name    : CSeparatedNPComplete.PolynomialCertificate.selector_count
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:50:58.948107+00:00
-- url     : https://prove2.me/theorems/00e5f29e-d573-4bdf-b19a-35ae79ed5478
-- title:
--   Polynomial Certificate: selector count
-- statement:
--   The Polynomial Certificate construction uses the selector count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/PolynomialCertificate.lean#L189-L195
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/PolynomialCertificate.lean#L189-L195

module
public import Definitions.Def_CSeparatedNPComplete_PartitionEquivalence
public import Mathlib.Data.Nat.Size
public import Definitions.Def_CSeparatedNPComplete_PolynomialCertificate
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete CSeparatedNPComplete.PolynomialCertificate

theorem CSeparatedNPComplete.PolynomialCertificate.selector_count {n : ℕ} (s : Fin n → ℕ) (b : Fin n → Bool) :
    dot (selector b) 1 = (leftCount (tagged s b) : ℝ) := by sorry

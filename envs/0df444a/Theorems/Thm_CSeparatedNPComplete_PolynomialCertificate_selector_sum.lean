-- Prove2me | Theorems.Thm_CSeparatedNPComplete_PolynomialCertificate_selector_sum
-- name    : CSeparatedNPComplete.PolynomialCertificate.selector_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:50:54.788281+00:00
-- url     : https://prove2.me/theorems/45cb6b1b-2421-5175-96ef-4580289f3dbb
-- title:
--   Polynomial Certificate: selector sum
-- statement:
--   The Polynomial Certificate construction uses the selector sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/PolynomialCertificate.lean#L197-L202
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/PolynomialCertificate.lean#L197-L202

module
public import Definitions.Def_CSeparatedNPComplete_PartitionEquivalence
public import Mathlib.Data.Nat.Size
public import Definitions.Def_CSeparatedNPComplete_PolynomialCertificate
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete CSeparatedNPComplete.PolynomialCertificate

theorem CSeparatedNPComplete.PolynomialCertificate.selector_sum {n : ℕ} (s : Fin n → ℕ) (b : Fin n → Bool) :
    dot (selector b) (fun i => (s i : ℝ)) = (leftSum (tagged s b) : ℝ) := by sorry

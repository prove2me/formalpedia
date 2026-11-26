-- Prove2me | Theorems.Thm_CSeparatedNPComplete_PolynomialCertificate_budget_le_inputBits
-- name    : CSeparatedNPComplete.PolynomialCertificate.budget_le_inputBits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:50:38.493449+00:00
-- url     : https://prove2.me/theorems/85565816-e301-4499-9d4f-4bb5f8f1746e
-- title:
--   Polynomial Certificate: budget le input Bits
-- statement:
--   The Polynomial Certificate construction uses the budget le input Bits property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/PolynomialCertificate.lean#L138-L145
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/PolynomialCertificate.lean#L138-L145

module
public import Definitions.Def_CSeparatedNPComplete_PartitionEquivalence
public import Mathlib.Data.Nat.Size
public import Definitions.Def_CSeparatedNPComplete_PolynomialCertificate
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete CSeparatedNPComplete.PolynomialCertificate

theorem CSeparatedNPComplete.PolynomialCertificate.budget_le_inputBits {n : ℕ} (s : Fin n → ℕ) (b : Fin n → Bool) :
    budget (tagged s b) ≤ 3 * inputBits s := by sorry

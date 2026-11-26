-- Prove2me | Theorems.Thm_CSeparatedNPComplete_PolynomialCertificate_run_mass_le
-- name    : CSeparatedNPComplete.PolynomialCertificate.run_mass_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:48:12.359009+00:00
-- url     : https://prove2.me/theorems/dbf4aa0f-4706-4b39-b300-979a8a3da926
-- title:
--   Polynomial Certificate: run mass le
-- statement:
--   The Polynomial Certificate construction uses the run mass le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/PolynomialCertificate.lean#L64-L75
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/PolynomialCertificate.lean#L64-L75

module
public import Definitions.Def_CSeparatedNPComplete_PartitionEquivalence
public import Mathlib.Data.Nat.Size
public import Definitions.Def_CSeparatedNPComplete_PolynomialCertificate
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete CSeparatedNPComplete.PolynomialCertificate

theorem CSeparatedNPComplete.PolynomialCertificate.run_mass_le (xs : List (ℕ × Bool)) : bitMass (run xs) ≤ budget xs := by sorry

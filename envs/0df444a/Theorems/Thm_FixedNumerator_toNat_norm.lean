-- Prove2me | Theorems.Thm_FixedNumerator_toNat_norm
-- name    : FixedNumerator.toNat_norm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:37:51.81181+00:00
-- url     : https://prove2.me/theorems/b688a9fb-542f-46cc-a32d-4c1bc81ac960
-- title:
--   Fixed Numerator: to Nat norm
-- statement:
--   The Fixed Numerator construction uses the to Nat norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/FixedNumerator/Split.lean#L75-L76
-- source:
--   https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/FixedNumerator/Split.lean#L75-L76

module
public import Definitions.Def_FixedNumerator_Local
public import Definitions.Def_FixedNumerator_Split
set_option autoImplicit true
@[expose] public section
public section
open Complex Finset
open FixedNumerator

theorem FixedNumerator.toNat_norm (c : GaussianInt) : (c.norm.toNat : ℤ) = c.norm := by sorry

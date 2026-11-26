-- Prove2me | Theorems.Thm_FixedNumerator_IsPrimary_pow
-- name    : FixedNumerator.IsPrimary.pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:35:10.522495+00:00
-- url     : https://prove2.me/theorems/1bf44917-7afb-58d8-9a7e-a9c0fb1e2456
-- title:
--   Is Primary: pow
-- statement:
--   The Is Primary construction uses the pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/FixedNumerator/Primary.lean#L31-L34
-- source:
--   https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/FixedNumerator/Primary.lean#L31-L34

module
public import Definitions.Def_FixedNumerator_Defs
public import Definitions.Def_FixedNumerator_Primary
set_option autoImplicit true
@[expose] public section
public section
open Complex Finset
open FixedNumerator

theorem FixedNumerator.IsPrimary.pow {a : GaussianInt} (ha : IsPrimary a) (k : ℕ) : IsPrimary (a ^ k) := by sorry

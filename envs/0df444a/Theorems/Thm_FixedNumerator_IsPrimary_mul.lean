-- Prove2me | Theorems.Thm_FixedNumerator_IsPrimary_mul
-- name    : FixedNumerator.IsPrimary.mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:35:14.373311+00:00
-- url     : https://prove2.me/theorems/cb1e864e-2a52-4196-b0ca-30125a96e544
-- title:
--   Is Primary: mul
-- statement:
--   The Is Primary construction uses the mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/FixedNumerator/Primary.lean#L23-L29
-- source:
--   https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/FixedNumerator/Primary.lean#L23-L29

module
public import Definitions.Def_FixedNumerator_Defs
public import Definitions.Def_FixedNumerator_Primary
set_option autoImplicit true
@[expose] public section
public section
open Complex Finset
open FixedNumerator

theorem FixedNumerator.IsPrimary.mul {a b : GaussianInt} (ha : IsPrimary a) (hb : IsPrimary b) :
    IsPrimary (a * b) := by sorry

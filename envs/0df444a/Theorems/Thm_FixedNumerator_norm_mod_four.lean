-- Prove2me | Theorems.Thm_FixedNumerator_norm_mod_four
-- name    : FixedNumerator.norm_mod_four
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:36:08.250344+00:00
-- url     : https://prove2.me/theorems/a10697ef-ea61-40ee-99ec-2333af7942ad
-- title:
--   Fixed Numerator: norm mod four
-- statement:
--   The Fixed Numerator construction uses the norm mod four property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/FixedNumerator/Primary.lean#L59-L64
-- source:
--   https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/FixedNumerator/Primary.lean#L59-L64

module
public import Definitions.Def_FixedNumerator_Defs
public import Definitions.Def_FixedNumerator_Primary
set_option autoImplicit true
@[expose] public section
public section
open Complex Finset
open FixedNumerator

theorem FixedNumerator.norm_mod_four {a : GaussianInt} (ha : IsPrimary a) : a.norm % 4 = 1 := by sorry

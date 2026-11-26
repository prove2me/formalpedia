-- Prove2me | Theorems.Thm_FixedNumerator_not_four_dvd_zero_sub
-- name    : FixedNumerator.not_four_dvd_zero_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:37:11.128457+00:00
-- url     : https://prove2.me/theorems/a9993ead-f9d3-4cf9-b7b9-0888ec631590
-- title:
--   Fixed Numerator: not four dvd zero sub
-- statement:
--   The Fixed Numerator construction uses the not four dvd zero sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/FixedNumerator/Split.lean#L52-L61
-- source:
--   https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/FixedNumerator/Split.lean#L52-L61

module
public import Definitions.Def_FixedNumerator_Local
public import Definitions.Def_FixedNumerator_Split
set_option autoImplicit true
@[expose] public section
public section
open Complex Finset
open FixedNumerator

theorem FixedNumerator.not_four_dvd_zero_sub {b : GaussianInt} (hb : IsPrimary b) :
    ¬ (4 : GaussianInt) ∣ 0 - b := by sorry

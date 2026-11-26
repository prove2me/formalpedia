-- Prove2me | Theorems.Thm_FixedNumerator_ne_zero_of_four_dvd
-- name    : FixedNumerator.ne_zero_of_four_dvd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:39:02.270456+00:00
-- url     : https://prove2.me/theorems/3e89fb43-a307-5f82-a018-18465531230f
-- title:
--   Fixed Numerator: ne zero of four dvd
-- statement:
--   The Fixed Numerator construction uses the ne zero of four dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/FixedNumerator/Split.lean#L63-L65
-- source:
--   https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/FixedNumerator/Split.lean#L63-L65

module
public import Definitions.Def_FixedNumerator_Local
public import Definitions.Def_FixedNumerator_Split
set_option autoImplicit true
@[expose] public section
public section
open Complex Finset
open FixedNumerator

theorem FixedNumerator.ne_zero_of_four_dvd {b c : GaussianInt} (hb : IsPrimary b) (h : (4 : GaussianInt) ∣ c - b) :
    c ≠ 0 := by sorry

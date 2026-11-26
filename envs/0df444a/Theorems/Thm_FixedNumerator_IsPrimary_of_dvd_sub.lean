-- Prove2me | Theorems.Thm_FixedNumerator_IsPrimary_of_dvd_sub
-- name    : FixedNumerator.IsPrimary.of_dvd_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:35:17.679056+00:00
-- url     : https://prove2.me/theorems/21d1be3d-6fc8-56dc-84fb-9a3a9933173b
-- title:
--   Is Primary: of dvd sub
-- statement:
--   The Is Primary construction uses the of dvd sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/FixedNumerator/Primary.lean#L38-L42
-- source:
--   https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/FixedNumerator/Primary.lean#L38-L42

module
public import Definitions.Def_FixedNumerator_Defs
public import Definitions.Def_FixedNumerator_Primary
set_option autoImplicit true
@[expose] public section
public section
open Complex Finset
open FixedNumerator

theorem FixedNumerator.IsPrimary.of_dvd_sub {a b : GaussianInt} (hb : IsPrimary b) (h : (4 : GaussianInt) ∣ a - b) :
    IsPrimary a := by sorry

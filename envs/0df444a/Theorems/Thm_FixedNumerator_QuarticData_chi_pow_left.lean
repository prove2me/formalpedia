-- Prove2me | Theorems.Thm_FixedNumerator_QuarticData_chi_pow_left
-- name    : FixedNumerator.QuarticData.chi_pow_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:35:30.704956+00:00
-- url     : https://prove2.me/theorems/0c10c118-cff9-591f-b2c3-c0c5831179be
-- title:
--   Quartic Data: chi pow left
-- statement:
--   The Quartic Data construction uses the chi pow left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/FixedNumerator/Local.lean#L55-L58
-- source:
--   https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/FixedNumerator/Local.lean#L55-L58

module
public import Definitions.Def_FixedNumerator_Primary
public import Definitions.Def_FixedNumerator_Local
set_option autoImplicit true
@[expose] public section
public section
open Complex Finset
open FixedNumerator
open FixedNumerator.QuarticData
variable (D : QuarticData)

theorem FixedNumerator.QuarticData.chi_pow_left (a c : GaussianInt) (n : ℕ) : D.χ (a ^ n) c = D.χ a c ^ n := by sorry

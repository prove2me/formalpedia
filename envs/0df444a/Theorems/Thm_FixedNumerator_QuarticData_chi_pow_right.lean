-- Prove2me | Theorems.Thm_FixedNumerator_QuarticData_chi_pow_right
-- name    : FixedNumerator.QuarticData.chi_pow_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:39:06.897942+00:00
-- url     : https://prove2.me/theorems/a242d9a8-1f11-4810-826d-b2b4f188367b
-- title:
--   Quartic Data: chi pow right
-- statement:
--   The Quartic Data construction uses the chi pow right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/FixedNumerator/Local.lean#L60-L64
-- source:
--   https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/FixedNumerator/Local.lean#L60-L64

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

theorem FixedNumerator.QuarticData.chi_pow_right (a : GaussianInt) {π : GaussianInt} (hπ : IsPrimary π) (n : ℕ) :
    D.χ a (π ^ n) = D.χ a π ^ n := by sorry

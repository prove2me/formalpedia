-- Prove2me | Theorems.Thm_FixedNumerator_QuarticData_g_eq_conj_chi_mul
-- name    : FixedNumerator.QuarticData.g_eq_conj_chi_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:40:51.531717+00:00
-- url     : https://prove2.me/theorems/a610b009-54c8-50fa-b07d-9516b9f49878
-- title:
--   Quartic Data: g eq conj chi mul
-- statement:
--   `g₄(ν, c) = conj((ν/c)₄) g₄(1, c)` for primary `c` prime to `ν` (Lemma 2.1(i)).
--
--   Source: https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/FixedNumerator/Local.lean#L103-L105
-- source:
--   https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/FixedNumerator/Local.lean#L103-L105

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

theorem FixedNumerator.QuarticData.g_eq_conj_chi_mul (ν : GaussianInt) {c : GaussianInt} (hc : IsPrimary c)
    (hcop : IsCoprime ν c) : D.g ν c = starRingEnd ℂ (D.χ ν c) * D.g 1 c := by sorry

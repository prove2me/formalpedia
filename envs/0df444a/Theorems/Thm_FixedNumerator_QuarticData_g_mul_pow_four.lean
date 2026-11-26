-- Prove2me | Theorems.Thm_FixedNumerator_QuarticData_g_mul_pow_four
-- name    : FixedNumerator.QuarticData.g_mul_pow_four
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:36:10.468999+00:00
-- url     : https://prove2.me/theorems/317ee083-e39d-401d-ac3d-4e54051a1c67
-- title:
--   Quartic Data: g mul pow four
-- statement:
--   `g₄(μ π^{4j}, c) = g₄(μ, c)` for primary `c` prime to `π`.
--
--   Source: https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/FixedNumerator/Local.lean#L97-L100
-- source:
--   https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/FixedNumerator/Local.lean#L97-L100

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

theorem FixedNumerator.QuarticData.g_mul_pow_four (μ : GaussianInt) {π c : GaussianInt} (hc : IsPrimary c)
    (hcop : IsCoprime π c) (j : ℕ) : D.g (μ * π ^ (4 * j)) c = D.g μ c := by sorry

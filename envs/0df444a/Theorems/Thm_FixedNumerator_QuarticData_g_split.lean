-- Prove2me | Theorems.Thm_FixedNumerator_QuarticData_g_split
-- name    : FixedNumerator.QuarticData.g_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:36:03.85013+00:00
-- url     : https://prove2.me/theorems/47d82c13-331b-4d69-b76b-9811e1e862cf
-- title:
--   Quartic Data: g split
-- statement:
--   **The splitting identity.** For a primary `π` and a primary `c'` prime to `π`,
--   `g₄(μ, π^k c') = (-1)^{C(c', π^k)} g₄(μ, π^k) g₄(μ π^{2k}, c')`. No condition links `μ` and `π`.
--
--   Source: https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/FixedNumerator/Local.lean#L80-L94
-- source:
--   https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/FixedNumerator/Local.lean#L80-L94

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

theorem FixedNumerator.QuarticData.g_split (μ : GaussianInt) {π c' : GaussianInt} (hπ : IsPrimary π) (hc' : IsPrimary c')
    (hcop : IsCoprime π c') (k : ℕ) :
    D.g μ (π ^ k * c') =
      (-1 : ℂ) ^ C c' (π ^ k) * D.g μ (π ^ k) * D.g (μ * π ^ (2 * k)) c' := by sorry

-- Prove2me | Theorems.Thm_FixedNumerator_QuarticData_g_mul_sq
-- name    : FixedNumerator.QuarticData.g_mul_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:35:57.992715+00:00
-- url     : https://prove2.me/theorems/c2e80fc3-fd46-423a-8478-1e8062163623
-- title:
--   Quartic Data: g mul sq
-- statement:
--   DDHL (3.6): `g₄(μ, c c') = (-1)^{C(c', c)} g₄(μ c'², c) g₄(μ, c')` for coprime primary
--   `c, c'`.
--
--   Source: https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/FixedNumerator/Local.lean#L68-L76
-- source:
--   https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/FixedNumerator/Local.lean#L68-L76

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

theorem FixedNumerator.QuarticData.g_mul_sq (μ : GaussianInt) {c c' : GaussianInt} (hc : IsPrimary c) (hc' : IsPrimary c')
    (hcc : IsCoprime c c') :
    D.g μ (c * c') = (-1 : ℂ) ^ C c' c * D.g (μ * c' ^ 2) c * D.g μ c' := by sorry

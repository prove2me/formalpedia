-- Prove2me | Theorems.Thm_FixedNumerator_QuarticData_truncSum_reduce_num
-- name    : FixedNumerator.QuarticData.truncSum_reduce_num
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:39:42.109604+00:00
-- url     : https://prove2.me/theorems/5c7000e3-1d5c-5cb2-b93c-87245161c8f1
-- title:
--   Quartic Data: trunc Sum reduce num
-- statement:
--   **Corollary 2.3, first claim.** `S_{πγ}(π^e μ', β)(X) = S_{πγ}(π^{e mod 4} μ', β)(X)`.
--
--   Source: https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/FixedNumerator/General.lean#L27-L32
-- source:
--   https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/FixedNumerator/General.lean#L27-L32

module
public import Definitions.Def_FixedNumerator_Cases
public import Definitions.Def_FixedNumerator_General
set_option autoImplicit true
@[expose] public section
public section
open Complex Finset
open FixedNumerator
open FixedNumerator.QuarticData
variable (D : QuarticData)

theorem FixedNumerator.QuarticData.truncSum_reduce_num (W : GaussianInt → ℂ) {π γ : GaussianInt} (μ' β : GaussianInt)
    (hβ : IsPrimary β) (e X : ℕ) :
    truncSum D W (π ^ e * μ') β (π * γ) X = truncSum D W (π ^ (e % 4) * μ') β (π * γ) X := by sorry

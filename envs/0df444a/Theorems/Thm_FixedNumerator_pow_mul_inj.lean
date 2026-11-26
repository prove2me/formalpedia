-- Prove2me | Theorems.Thm_FixedNumerator_pow_mul_inj
-- name    : FixedNumerator.pow_mul_inj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:39:52.495044+00:00
-- url     : https://prove2.me/theorems/8a460b43-ab53-4fb8-ab1c-b8afb514f962
-- title:
--   Fixed Numerator: pow mul inj
-- statement:
--   Uniqueness of `c = π^k c'` with `π ∤ c'`.
--
--   Source: https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/FixedNumerator/Split.lean#L85-L101
-- source:
--   https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/FixedNumerator/Split.lean#L85-L101

module
public import Definitions.Def_FixedNumerator_Local
public import Definitions.Def_FixedNumerator_Split
set_option autoImplicit true
@[expose] public section
public section
open Complex Finset
open FixedNumerator

theorem FixedNumerator.pow_mul_inj {π a b : GaussianInt} (hπ : Prime π) (ha : ¬ π ∣ a) (hb : ¬ π ∣ b) {k j : ℕ}
    (h : π ^ k * a = π ^ j * b) : k = j ∧ a = b := by sorry

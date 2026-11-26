-- Prove2me | Theorems.Thm_FixedNumerator_two_le_norm_of_prime
-- name    : FixedNumerator.two_le_norm_of_prime
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:36:43.860735+00:00
-- url     : https://prove2.me/theorems/007ce37d-bc8e-4dc6-acdf-22cc1f905084
-- title:
--   Fixed Numerator: two le norm of prime
-- statement:
--   The Fixed Numerator construction uses the two le norm of prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/FixedNumerator/Split.lean#L67-L73
-- source:
--   https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/FixedNumerator/Split.lean#L67-L73

module
public import Definitions.Def_FixedNumerator_Local
public import Definitions.Def_FixedNumerator_Split
set_option autoImplicit true
@[expose] public section
public section
open Complex Finset
open FixedNumerator

theorem FixedNumerator.two_le_norm_of_prime {π : GaussianInt} (hπ : Prime π) : 2 ≤ π.norm := by sorry

-- Prove2me | Theorems.Thm_FixedNumerator_le_div_iff_norm
-- name    : FixedNumerator.le_div_iff_norm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:39:27.526985+00:00
-- url     : https://prove2.me/theorems/97e3a2c5-9cfb-441a-a55c-9ba3fecea659
-- title:
--   Fixed Numerator: le div iff norm
-- statement:
--   The Fixed Numerator construction uses the le div iff norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/FixedNumerator/Split.lean#L78-L82
-- source:
--   https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/FixedNumerator/Split.lean#L78-L82

module
public import Definitions.Def_FixedNumerator_Local
public import Definitions.Def_FixedNumerator_Split
set_option autoImplicit true
@[expose] public section
public section
open Complex Finset
open FixedNumerator

theorem FixedNumerator.le_div_iff_norm {X M : ℕ} (hM : 0 < M) (c : GaussianInt) :
    c.norm ≤ ((X / M : ℕ) : ℤ) ↔ (M : ℤ) * c.norm ≤ X := by sorry

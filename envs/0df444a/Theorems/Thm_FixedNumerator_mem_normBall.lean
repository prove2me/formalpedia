-- Prove2me | Theorems.Thm_FixedNumerator_mem_normBall
-- name    : FixedNumerator.mem_normBall
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:36:51.827129+00:00
-- url     : https://prove2.me/theorems/880144e6-43e7-4c05-a46c-d2ec6b129707
-- title:
--   Fixed Numerator: mem norm Ball
-- statement:
--   The Fixed Numerator construction uses the mem norm Ball property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/FixedNumerator/Split.lean#L30-L41
-- source:
--   https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/FixedNumerator/Split.lean#L30-L41

module
public import Definitions.Def_FixedNumerator_Local
public import Definitions.Def_FixedNumerator_Split
set_option autoImplicit true
@[expose] public section
public section
open Complex Finset
open FixedNumerator

theorem FixedNumerator.mem_normBall {X : ℕ} {c : GaussianInt} : c ∈ normBall X ↔ c.norm ≤ X := by sorry

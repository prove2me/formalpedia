-- Prove2me | Theorems.Thm_FixedNumerator_quarter_parity
-- name    : FixedNumerator.quarter_parity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:36:21.333221+00:00
-- url     : https://prove2.me/theorems/acc3189b-46a6-4539-9b9a-7aca453fac2e
-- title:
--   Fixed Numerator: quarter parity
-- statement:
--   The parity of `(N a - 1)/4` depends only on the class of a primary `a` modulo `4`.
--
--   Source: https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/FixedNumerator/Primary.lean#L74-L78
-- source:
--   https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/FixedNumerator/Primary.lean#L74-L78

module
public import Definitions.Def_FixedNumerator_Defs
public import Definitions.Def_FixedNumerator_Primary
set_option autoImplicit true
@[expose] public section
public section
open Complex Finset
open FixedNumerator

theorem FixedNumerator.quarter_parity {a b : GaussianInt} (hb : IsPrimary b) (h : (4 : GaussianInt) ∣ a - b) :
    (a.norm - 1) / 4 % 2 = (b.norm - 1) / 4 % 2 := by sorry

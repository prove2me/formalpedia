-- Prove2me | Theorems.Thm_BandParity_sum_char_mul
-- name    : BandParity.sum_char_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:01:51.877481+00:00
-- url     : https://prove2.me/theorems/42b5991c-d4e2-43df-ba26-884d9efa0ab5
-- title:
--   Band Parity: sum char mul
-- statement:
--   Grouping `∑ χ(x) g(x)` by the four classes.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Laws.lean#L175-L185
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Laws.lean#L175-L185

module
public import Definitions.Def_BandParity_Defs
public import Definitions.Def_BandParity_Matching
public import Definitions.Def_BandParity_Laws
set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hχ : orderOf χ = 4)
include hχ

theorem BandParity.sum_char_mul (g : ZMod p → ℤ) :
    ∑ x, χ x * (g x : GaussianInt) =
      ((∑ x ∈ cls χ 1, g x : ℤ) : GaussianInt) + gi * ((∑ x ∈ cls χ gi, g x : ℤ) : GaussianInt)
        - ((∑ x ∈ cls χ (-1), g x : ℤ) : GaussianInt)
        - gi * ((∑ x ∈ cls χ (-gi), g x : ℤ) : GaussianInt) := by sorry

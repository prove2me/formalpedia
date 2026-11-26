-- Prove2me | Theorems.Thm_BandParity_sum_char_mul_odd
-- name    : BandParity.sum_char_mul_odd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:01:59.15325+00:00
-- url     : https://prove2.me/theorems/352a5dba-feb7-49d7-9191-62619c01c184
-- title:
--   Band Parity: sum char mul odd
-- statement:
--   The Band Parity construction uses the sum char mul odd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Laws.lean#L227-L232
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Laws.lean#L227-L232

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

theorem BandParity.sum_char_mul_odd (hodd : χ (-1) = -1) (g : ZMod p → ℤ) (hg : ∀ x ≠ 0, g (-x) = -g x) :
    ∑ x, χ x * (g x : GaussianInt) =
      2 * (((∑ x ∈ cls χ 1, g x : ℤ) : GaussianInt)
        + gi * ((∑ x ∈ cls χ gi, g x : ℤ) : GaussianInt)) := by sorry

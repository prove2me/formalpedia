-- Prove2me | Theorems.Thm_BandParity_two_mul_bijOn_gi
-- name    : BandParity.two_mul_bijOn_gi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:07:12.094881+00:00
-- url     : https://prove2.me/theorems/b6c79628-cc57-58bd-9377-f86434141c34
-- title:
--   Band Parity: two mul bij On gi
-- statement:
--   The Band Parity construction uses the two mul bij On gi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Main.lean#L166-L171
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Main.lean#L166-L171

module
public import Definitions.Def_BandParity_Laws
public import Definitions.Def_BandParity_Main
set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hχ : orderOf χ = 4)
include hχ

theorem BandParity.two_mul_bijOn_gi (hp8 : p % 8 = 5) (hpin : χ 2 = gi) :
    Set.BijOn (fun x : ZMod p => 2 * x) (cls χ gi : Set (ZMod p))
      (cls χ (-1) : Set (ZMod p)) := by sorry

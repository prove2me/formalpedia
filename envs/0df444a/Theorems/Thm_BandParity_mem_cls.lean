-- Prove2me | Theorems.Thm_BandParity_mem_cls
-- name    : BandParity.mem_cls
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:05:13.055789+00:00
-- url     : https://prove2.me/theorems/bfe166d8-7882-47b5-a193-7bd942c52bd6
-- title:
--   Band Parity: mem cls
-- statement:
--   The Band Parity construction uses the mem cls property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Main.lean#L126-L127
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Main.lean#L126-L127

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
omit hχ

theorem BandParity.mem_cls {z : GaussianInt} {x : ZMod p} : x ∈ (cls χ z : Set (ZMod p)) ↔ χ x = z := by sorry

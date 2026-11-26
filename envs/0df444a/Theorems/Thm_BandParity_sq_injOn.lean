-- Prove2me | Theorems.Thm_BandParity_sq_injOn
-- name    : BandParity.sq_injOn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:05:09.427508+00:00
-- url     : https://prove2.me/theorems/2dee2864-87fd-51d7-b1f9-4a9f1e0fa20e
-- title:
--   Band Parity: sq inj On
-- statement:
--   The Band Parity construction uses the sq inj On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Main.lean#L129-L138
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Main.lean#L129-L138

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

theorem BandParity.sq_injOn (hp8 : p % 8 = 5) {z : GaussianInt} (hz : z ≠ 0) :
    Set.InjOn (fun x : ZMod p => x ^ 2) (cls χ z : Set (ZMod p)) := by sorry

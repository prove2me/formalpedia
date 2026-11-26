-- Prove2me | Theorems.Thm_BandParity_sq_bijOn_gi
-- name    : BandParity.sq_bijOn_gi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:05:55.632045+00:00
-- url     : https://prove2.me/theorems/65e23dee-7b0e-4c0b-b316-cb56a7ccdad5
-- title:
--   Band Parity: sq bij On gi
-- statement:
--   The Band Parity construction uses the sq bij On gi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Main.lean#L160-L164
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Main.lean#L160-L164

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

theorem BandParity.sq_bijOn_gi (hp8 : p % 8 = 5) :
    Set.BijOn (fun x : ZMod p => x ^ 2) (cls χ gi : Set (ZMod p))
      (cls χ (-1) : Set (ZMod p)) := by sorry

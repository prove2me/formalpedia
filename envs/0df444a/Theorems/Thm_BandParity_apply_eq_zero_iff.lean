-- Prove2me | Theorems.Thm_BandParity_apply_eq_zero_iff
-- name    : BandParity.apply_eq_zero_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:54:40.367045+00:00
-- url     : https://prove2.me/theorems/5eabe5fe-4b51-55d8-a114-0f0d5c81ced3
-- title:
--   Band Parity: apply eq zero iff
-- statement:
--   The Band Parity construction uses the apply eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/CosetSums.lean#L51-L54
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/CosetSums.lean#L51-L54

module
public import Definitions.Def_BandParity_Pin
public import Definitions.Def_BandParity_FixedBase
public import Definitions.Def_BandParity_CosetSums
set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hχ : orderOf χ = 4)
include hχ

theorem BandParity.apply_eq_zero_iff {n : ZMod p} : χ n = 0 ↔ n = 0 := by sorry

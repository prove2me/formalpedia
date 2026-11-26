-- Prove2me | Theorems.Thm_BandParity_t_pow_three
-- name    : BandParity.t_pow_three
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:56:09.260433+00:00
-- url     : https://prove2.me/theorems/a63680ae-9c0e-46bd-8c93-3fae9b32bc1c
-- title:
--   Band Parity: t pow three
-- statement:
--   **Conjugation.** `χ ↦ χ̄` negates `t`.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/CosetSums.lean#L235-L237
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/CosetSums.lean#L235-L237

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

theorem BandParity.t_pow_three : t (χ ^ 3) = -t χ := by sorry

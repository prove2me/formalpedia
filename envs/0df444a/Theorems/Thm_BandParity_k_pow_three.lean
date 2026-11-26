-- Prove2me | Theorems.Thm_BandParity_k_pow_three
-- name    : BandParity.k_pow_three
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:56:08.134077+00:00
-- url     : https://prove2.me/theorems/8530330e-f888-59e6-8b67-15eca1bc9302
-- title:
--   Band Parity: k pow three
-- statement:
--   **Conjugation.** `χ ↦ χ̄` fixes `k`.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/CosetSums.lean#L230-L232
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/CosetSums.lean#L230-L232

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

theorem BandParity.k_pow_three : k (χ ^ 3) = k χ := by sorry

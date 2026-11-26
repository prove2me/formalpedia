-- Prove2me | Theorems.Thm_BandParity_bandSum_re
-- name    : BandParity.bandSum_re
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:13:22.489117+00:00
-- url     : https://prove2.me/theorems/b391a9a4-37c9-4ea9-824d-7cde7a8086c6
-- title:
--   Band Parity: band Sum re
-- statement:
--   **Coset form, real part.** `f = ∑_{u ∈ H} s(u) s(u²)`.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/Solution.lean#L71-L73
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/Solution.lean#L71-L73

module
public import Definitions.Def_BandParity
public import Definitions.Def_BandParity_Solution
set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hχ : orderOf χ = 4)
include hχ

theorem BandParity.bandSum_re (hp8 : p % 8 = 5) :
    (bandSum χ).re = ∑ u ∈ cls χ 1, parSign u * parSign (u ^ 2) := by sorry

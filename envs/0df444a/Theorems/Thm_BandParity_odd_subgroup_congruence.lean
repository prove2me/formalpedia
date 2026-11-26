-- Prove2me | Theorems.Thm_BandParity_odd_subgroup_congruence
-- name    : BandParity.odd_subgroup_congruence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:14:22.794107+00:00
-- url     : https://prove2.me/theorems/42f646e0-8acb-4e0e-83c1-282f3460fc58
-- title:
--   Band Parity: odd subgroup congruence
-- statement:
--   **Theorem B (the odd-subgroup congruence).**
--   `T^{(e)}_{H,x}(N) ≡ |H| - 2 α(xH) - 2 α((xH)^e) (mod 4)`.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/Solution.lean#L129-L133
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/Solution.lean#L129-L133

module
public import Definitions.Def_BandParity
public import Definitions.Def_BandParity_Solution
set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
variable {N : ℕ} [NeZero N] (hN : Odd N) (hN3 : 3 ≤ N)
variable {H : Subgroup (ZMod N)ˣ} [DecidablePred (· ∈ H)] (hH : Odd (Nat.card H))
include hN hN3 hH

theorem BandParity.odd_subgroup_congruence (x : (ZMod N)ˣ) {e : ℕ} (he : Even e) (he0 : e ≠ 0) :
    cosetBandSum H x e ≡
      (Nat.card H : ℤ) - 2 * oddCount (coset H x) - 2 * oddCount ((coset H x).image (· ^ e))
      [ZMOD 4] := by sorry

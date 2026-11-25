-- Prove2me | Theorems.Thm_ConjCoord_Proof_pell2_even
-- name    : ConjCoord.Proof.pell2_even
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:53:14.795404+00:00
-- url     : https://prove2.me/theorems/f9e5b78d-f0af-499d-b81f-7f5341ab6f79
-- title:
--   Proof: pell2 even
-- statement:
--   The Pell equation `R'² - 2p S'² = 1` with `p ≡ 5 (mod 8)` forces `S'` to be even: if `S'` were
--   odd, then `R'² ≡ 1 + 2p ≡ 3 (mod 8)`.
--
--   Source: https://github.com/jkfarland-bot/ConjCoord/blob/c956f4808ba6c6f15a1d4234a04cd8fc56be2711/ConjCoord/Main.lean#L244-L258
-- source:
--   https://github.com/jkfarland-bot/ConjCoord/blob/c956f4808ba6c6f15a1d4234a04cd8fc56be2711/ConjCoord/Main.lean#L244-L258

module
public import Definitions.Def_ConjCoord_Compute
public import Definitions.Def_ConjCoord_TwoSquares
public import Definitions.Def_ConjCoord_Main
set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord ConjCoord.Proof

theorem ConjCoord.Proof.pell2_even {p : ℕ} (h5 : p % 16 = 5) {R S : ℤ}
    (hP : R ^ 2 - 2 * (p : ℤ) * S ^ 2 = 1) : Even S := by sorry

-- Prove2me | Theorems.Thm_ConjCoord_Proof_pell_even
-- name    : ConjCoord.Proof.pell_even
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:53:09.562236+00:00
-- url     : https://prove2.me/theorems/54340c54-2486-4247-9488-335cf4e025b4
-- title:
--   Proof: pell even
-- statement:
--   The Pell equation `R² - p S² = 1` with `p ≡ 5 (mod 8)` forces `S` to be even: if `S` were odd,
--   then `R² ≡ 1 + p ≡ 6 (mod 8)`.
--
--   Source: https://github.com/jkfarland-bot/ConjCoord/blob/c956f4808ba6c6f15a1d4234a04cd8fc56be2711/ConjCoord/Main.lean#L226-L240
-- source:
--   https://github.com/jkfarland-bot/ConjCoord/blob/c956f4808ba6c6f15a1d4234a04cd8fc56be2711/ConjCoord/Main.lean#L226-L240

module
public import Definitions.Def_ConjCoord_Compute
public import Definitions.Def_ConjCoord_TwoSquares
public import Definitions.Def_ConjCoord_Main
set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord ConjCoord.Proof

theorem ConjCoord.Proof.pell_even {p : ℕ} (h5 : p % 16 = 5) {R S : ℤ} (hP : R ^ 2 - (p : ℤ) * S ^ 2 = 1) :
    Even S := by sorry

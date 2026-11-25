-- Prove2me | Theorems.Thm_ConjCoord_Proof_tCoeff_dvd
-- name    : ConjCoord.Proof.tCoeff_dvd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:53:04.432802+00:00
-- url     : https://prove2.me/theorems/00b4bfd2-a721-42f1-9ccd-2c4b14270b13
-- title:
--   Proof: t Coeff dvd
-- statement:
--   Inverting `θ(1)`: `64 ∣ T(m)` for all `m`.
--
--   Source: https://github.com/jkfarland-bot/ConjCoord/blob/c956f4808ba6c6f15a1d4234a04cd8fc56be2711/ConjCoord/Main.lean#L85-L102
-- source:
--   https://github.com/jkfarland-bot/ConjCoord/blob/c956f4808ba6c6f15a1d4234a04cd8fc56be2711/ConjCoord/Main.lean#L85-L102

module
public import Definitions.Def_ConjCoord_Compute
public import Definitions.Def_ConjCoord_TwoSquares
public import Definitions.Def_ConjCoord_Main
set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord ConjCoord.Proof

theorem ConjCoord.Proof.tCoeff_dvd (S : SturmInput phi 512) (m : ℕ) : (64 : ℤ) ∣ tCoeff m := by sorry

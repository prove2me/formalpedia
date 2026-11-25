-- Prove2me | Theorems.Thm_ConjCoord_Proof_tCoeff_check
-- name    : ConjCoord.Proof.tCoeff_check
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:46:07.614215+00:00
-- url     : https://prove2.me/theorems/aa98d3ec-f65c-4908-b264-080193d11322
-- title:
--   Proof: t Coeff check
-- statement:
--   **The finite check**: `64 ∣ tCoeff m` for `m ≤ 512`.
--
--   Source: https://github.com/jkfarland-bot/ConjCoord/blob/c956f4808ba6c6f15a1d4234a04cd8fc56be2711/ConjCoord/Compute.lean#L234-L235
-- source:
--   https://github.com/jkfarland-bot/ConjCoord/blob/c956f4808ba6c6f15a1d4234a04cd8fc56be2711/ConjCoord/Compute.lean#L234-L235

module
public import Definitions.Def_ConjCoord_Defs
public import Definitions.Def_ConjCoord_Compute
set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord ConjCoord.Proof

theorem ConjCoord.Proof.tCoeff_check (m : ℕ) (hm : m ≤ 512) : (64 : ℤ) ∣ tCoeff m := by sorry

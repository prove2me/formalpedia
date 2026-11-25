-- Prove2me | Theorems.Thm_ConjCoord_Proof_phi_dvd_of
-- name    : ConjCoord.Proof.phi_dvd_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:52:26.56207+00:00
-- url     : https://prove2.me/theorems/d09c7c0d-3e73-44fc-9f06-704c212292ad
-- title:
--   Proof: phi dvd of
-- statement:
--   The Proof construction uses the phi dvd of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/ConjCoord/blob/c956f4808ba6c6f15a1d4234a04cd8fc56be2711/ConjCoord/Main.lean#L63-L73
-- source:
--   https://github.com/jkfarland-bot/ConjCoord/blob/c956f4808ba6c6f15a1d4234a04cd8fc56be2711/ConjCoord/Main.lean#L63-L73

module
public import Definitions.Def_ConjCoord_Compute
public import Definitions.Def_ConjCoord_TwoSquares
public import Definitions.Def_ConjCoord_Main
set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord ConjCoord.Proof

theorem ConjCoord.Proof.phi_dvd_of {n : ℕ} (h : ∀ m ≤ n, (64 : ℤ) ∣ tCoeff m) : (256 : ℤ) ∣ phi n := by sorry

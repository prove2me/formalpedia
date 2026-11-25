-- Prove2me | Theorems.Thm_ConjCoord_Proof_eight_dvd_card_k_ne
-- name    : ConjCoord.Proof.eight_dvd_card_k_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:50:27.584523+00:00
-- url     : https://prove2.me/theorems/1f7ccda9-97a9-4bf0-8cab-19ee199de669
-- title:
--   Proof: eight dvd card k ne
-- statement:
--   The triples with `k ≠ 0` come in groups of `8`.
--
--   Source: https://github.com/jkfarland-bot/ConjCoord/blob/c956f4808ba6c6f15a1d4234a04cd8fc56be2711/ConjCoord/TwoSquares.lean#L111-L156
-- source:
--   https://github.com/jkfarland-bot/ConjCoord/blob/c956f4808ba6c6f15a1d4234a04cd8fc56be2711/ConjCoord/TwoSquares.lean#L111-L156

module
public import Definitions.Def_ConjCoord_Reps
public import Definitions.Def_ConjCoord_TwoSquares
set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord ConjCoord.Proof

theorem ConjCoord.Proof.eight_dvd_card_k_ne {m : ℕ} :
    8 ∣ ((gset m).filter fun v => ¬ v.2.2 = 0).card := by sorry

-- Prove2me | Theorems.Thm_BandParity_bijOn_of_injOn_card
-- name    : BandParity.bijOn_of_injOn_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:04:40.160664+00:00
-- url     : https://prove2.me/theorems/d0751cce-71c8-53cb-84f5-e28db68a9e59
-- title:
--   Band Parity: bij On of inj On card
-- statement:
--   An injective map between finite sets with `|t| ≤ |s|` is a bijection onto `t`.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Main.lean#L30-L40
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Main.lean#L30-L40

module
public import Definitions.Def_BandParity_Laws
public import Definitions.Def_BandParity_Main
set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
omit hp

theorem BandParity.bijOn_of_injOn_card {α β : Type*} [DecidableEq β] {s : Finset α} {t : Finset β}
    {f : α → β} (hm : Set.MapsTo f s t) (hi : Set.InjOn f s) (hc : t.card ≤ s.card) :
    Set.BijOn f s t := by sorry

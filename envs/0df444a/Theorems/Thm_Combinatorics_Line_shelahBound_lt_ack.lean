-- Prove2me | Theorems.Thm_Combinatorics_Line_shelahBound_lt_ack
-- name    : Combinatorics.Line.shelahBound_lt_ack
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:50:59.996836+00:00
-- url     : https://prove2.me/theorems/24779302-2380-4095-8f12-72e9f62aa1df
-- title:
--   Line: shelah Bound lt ack
-- statement:
--   Shelah's bound is below the fifth level of the Ackermann function.
--
--   Source: https://github.com/gdahia/ShelahHalesJewett/blob/8a91fc0e8a9617f8ade16ccb3b56e543990c9f45/ShelahHalesJewett/Ackermann.lean#L88-L91
-- source:
--   https://github.com/gdahia/ShelahHalesJewett/blob/8a91fc0e8a9617f8ade16ccb3b56e543990c9f45/ShelahHalesJewett/Ackermann.lean#L88-L91

module
public import Mathlib.Computability.Ackermann
public import Definitions.Def_ShelahHalesJewett_HalesJewett
public import Definitions.Def_ShelahHalesJewett_Ackermann
set_option autoImplicit true
@[expose] public section
public section
open Combinatorics
open Combinatorics.Line

theorem Combinatorics.Line.shelahBound_lt_ack (k r : ℕ) : shelahBound k r < ack 5 (2 * k + r) := by sorry

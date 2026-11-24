-- Prove2me | Theorems.Thm_Combinatorics_Subspace_insensitiveBound_le_ack
-- name    : Combinatorics.Subspace.insensitiveBound_le_ack
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:50:54.069201+00:00
-- url     : https://prove2.me/theorems/b2e31cc7-410c-475c-9591-9faa8d3f53c6
-- title:
--   Subspace: insensitive Bound le ack
-- statement:
--   The dimension `insensitiveBound k n r` is at most the fourth level of the Ackermann function
--   at a linear function of `n`.
--
--   Source: https://github.com/gdahia/ShelahHalesJewett/blob/8a91fc0e8a9617f8ade16ccb3b56e543990c9f45/ShelahHalesJewett/Ackermann.lean#L67-L69
-- source:
--   https://github.com/gdahia/ShelahHalesJewett/blob/8a91fc0e8a9617f8ade16ccb3b56e543990c9f45/ShelahHalesJewett/Ackermann.lean#L67-L69

module
public import Mathlib.Computability.Ackermann
public import Definitions.Def_ShelahHalesJewett_HalesJewett
public import Definitions.Def_ShelahHalesJewett_Ackermann
set_option autoImplicit true
@[expose] public section
public section
open Combinatorics
open Combinatorics.Subspace

theorem Combinatorics.Subspace.insensitiveBound_le_ack (k n r : ℕ) :
    insensitiveBound k n r ≤ ack 4 (5 * n + k + r + 2) := by sorry

-- Prove2me | Theorems.Thm_F6ConvexWindow_w3_chain_decomposition
-- name    : F6ConvexWindow.w3_chain_decomposition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:38:03.654575+00:00
-- url     : https://prove2.me/theorems/85043fc0-4ac8-42ab-a8b3-2dba26bb7606
-- title:
--   F6 Convex Window: w3 chain decomposition
-- statement:
--   The only width-three instance of the generic Dilworth theorem.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindowFull.lean#L54-L59
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindowFull.lean#L54-L59

import Definitions.Def_StableMarriageF6_F6ConvexWindow
import Definitions.Def_StableMarriageF6_DilworthTheorem
import Definitions.Def_StableMarriageF6_F6ConvexWindowFull
set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
variable {V : Type*} [Fintype V] [PartialOrder V]

theorem F6ConvexWindow.w3_chain_decomposition (hw : WidthLE (V := V) 3) :
    Nonempty (ChainDecomposition (V := V) 3) := by sorry

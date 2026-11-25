-- Prove2me | Theorems.Thm_F6ConvexWindow_width2_chain_decomposition
-- name    : F6ConvexWindow.width2_chain_decomposition
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T10:13:07.765817+00:00
-- url     : https://prove2.me/theorems/b92eb706-b02d-4fea-93e4-ccb03406f9b1
-- title:
--   F6 Convex Window: width2 chain decomposition
-- statement:
--   The only width-two instance of the generic Dilworth theorem.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindowFull.lean#L62-L67
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindowFull.lean#L62-L67

import Definitions.Def_StableMarriageF6_F6ConvexWindow
import Definitions.Def_StableMarriageF6_DilworthTheorem
import Definitions.Def_StableMarriageF6_F6ConvexWindowFull
set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
variable {V : Type*} [Fintype V] [PartialOrder V]

theorem F6ConvexWindow.width2_chain_decomposition (hw : WidthLE (V := V) 2) :
    Nonempty (ChainDecomposition (V := V) 2) := by sorry

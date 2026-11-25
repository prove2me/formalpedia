-- Prove2me | Theorems.Thm_F6ConvexWindow_degree_sum_eq_twice_A2
-- name    : F6ConvexWindow.degree_sum_eq_twice_A2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:08:38.245109+00:00
-- url     : https://prove2.me/theorems/32a55562-278f-45b6-b7f7-74124502ad1f
-- title:
--   F6 Convex Window: degree sum eq twice A2
-- statement:
--   §8 double count: each actual two-element antichain contributes exactly two incidences.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindow.lean#L525-L541
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindow.lean#L525-L541

import Mathlib
import Definitions.Def_StableMarriageF6_F6ConvexWindow
set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]

theorem F6ConvexWindow.degree_sum_eq_twice_A2 : (∑ x : V, (Inc x).card) = 2 * Ak (V := V) 2 := by sorry

-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_badCount_subset_biUnion
-- name    : FirstPassageLinearTransport.badCount_subset_biUnion
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T10:56:40.799986+00:00
-- url     : https://prove2.me/theorems/ae7d8ba1-3c5a-466d-a51b-344e70464203
-- title:
--   First Passage Linear Transport: bad Count subset bi Union
-- statement:
--   Every positive bad integer up to `X` lies in a shell of index at most
--   `Nat.log 2 X`.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Density.lean#L127-L140
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Density.lean#L127-L140

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_FirstPassageLinearTransport_Basic
import Definitions.Def_FirstPassageLinearTransport_Density
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section

theorem FirstPassageLinearTransport.badCount_subset_biUnion (S : Set ℕ) (X : ℕ) :
    prefixBad S X ⊆
      (Finset.range (Nat.log 2 X + 1)).biUnion (shellBad S) := by sorry

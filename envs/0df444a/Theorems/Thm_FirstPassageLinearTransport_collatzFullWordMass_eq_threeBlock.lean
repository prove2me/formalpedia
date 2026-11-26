-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_collatzFullWordMass_eq_threeBlock
-- name    : FirstPassageLinearTransport.collatzFullWordMass_eq_threeBlock
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:35:49.907846+00:00
-- url     : https://prove2.me/theorems/c887fba7-a62d-483a-96ec-6fa2dd68378d
-- title:
--   First Passage Linear Transport: collatz Full Word Mass eq three Block
-- statement:
--   Splitting a full word into its two outer blocks and middle block preserves
--   the exact Bernoulli mass.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L2139-L2156
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L2139-L2156

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.collatzFullWordMass_eq_threeBlock
    (p : ℝ) (a b : ℕ) (B q : ℝ) :
    collatzFullWordMass p (a + (b + a)) B q =
      collatzFullThreeBlockMass p a b B q := by sorry

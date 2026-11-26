-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_collatzFullThreeBlockMass_le_envelope
-- name    : FirstPassageLinearTransport.collatzFullThreeBlockMass_le_envelope
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:35:39.29306+00:00
-- url     : https://prove2.me/theorems/ad683696-cbac-4f06-a45f-faf76a7573ea
-- title:
--   First Passage Linear Transport: collatz Full Three Block Mass le envelope
-- statement:
--   Full surviving words form a subset of the three-block envelope.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L2159-L2183
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L2159-L2183

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.collatzFullThreeBlockMass_le_envelope
    (a b : ℕ) (B q : ℝ) :
    collatzFullThreeBlockMass (1 / 2) a b B q ≤
      collatzThreeBlockFlatMass (1 / 2) a b B q := by sorry

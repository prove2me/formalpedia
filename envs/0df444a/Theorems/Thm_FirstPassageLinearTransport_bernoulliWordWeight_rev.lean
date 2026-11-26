-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_bernoulliWordWeight_rev
-- name    : FirstPassageLinearTransport.bernoulliWordWeight_rev
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:34:14.941676+00:00
-- url     : https://prove2.me/theorems/8939faf6-f76f-4da3-8908-ae196468c0c3
-- title:
--   First Passage Linear Transport: bernoulli Word Weight rev
-- statement:
--   Reversing a finite word preserves its Bernoulli product weight.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L1420-L1426
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L1420-L1426

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.bernoulliWordWeight_rev
    {p : ℝ} {a : ℕ} (w : Fin a → Bool) :
    bernoulliWordWeight p (fun i => w (Fin.rev i)) =
      bernoulliWordWeight p w := by sorry

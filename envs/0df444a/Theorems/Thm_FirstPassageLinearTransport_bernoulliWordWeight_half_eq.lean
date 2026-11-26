-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_bernoulliWordWeight_half_eq
-- name    : FirstPassageLinearTransport.bernoulliWordWeight_half_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:30:04.010217+00:00
-- url     : https://prove2.me/theorems/f3f9e3a8-5e66-463e-b874-932fd052cdef
-- title:
--   First Passage Linear Transport: bernoulli Word Weight half eq
-- statement:
--   The First Passage Linear Transport construction uses the bernoulli Word Weight half eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L1748-L1756
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L1748-L1756

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.bernoulliWordWeight_half_eq {m : ℕ} (v : Fin m → Bool) :
    bernoulliWordWeight (1 / 2) v = (1 / 2 : ℝ) ^ m := by sorry

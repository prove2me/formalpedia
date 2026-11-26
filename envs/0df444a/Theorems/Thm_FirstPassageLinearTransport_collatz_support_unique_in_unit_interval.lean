-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_collatz_support_unique_in_unit_interval
-- name    : FirstPassageLinearTransport.collatz_support_unique_in_unit_interval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:32:40.054721+00:00
-- url     : https://prove2.me/theorems/fd343f7e-d4ce-5320-8dac-b1b9e40551ed
-- title:
--   First Passage Linear Transport: collatz support unique in unit interval
-- statement:
--   An interval of length one contains at most one support count for the
--   Collatz logarithmic lattice.  The decisive spacing is `log 3 > 1`.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L964-L1002
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L964-L1002

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.collatz_support_unique_in_unit_interval
    {k l : ℕ} {a : ℝ}
    (hklo : a ≤ (k : ℝ) * Real.log 3)
    (hkhi : (k : ℝ) * Real.log 3 < a + 1)
    (hllo : a ≤ (l : ℝ) * Real.log 3)
    (hlhi : (l : ℝ) * Real.log 3 < a + 1) :
    k = l := by sorry

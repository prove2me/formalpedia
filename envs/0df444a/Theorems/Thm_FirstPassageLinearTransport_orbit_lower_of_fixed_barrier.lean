-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_orbit_lower_of_fixed_barrier
-- name    : FirstPassageLinearTransport.orbit_lower_of_fixed_barrier
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:01:41.985644+00:00
-- url     : https://prove2.me/theorems/f8a1483c-6126-515b-96d4-4487e6ae33e3
-- title:
--   First Passage Linear Transport: orbit lower of fixed barrier
-- statement:
--   The First Passage Linear Transport construction uses the orbit lower of fixed barrier property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Envelope.lean#L452-L482
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Envelope.lean#L452-L482

import Mathlib.Algebra.Ring.GeomSum
import Definitions.Def_FirstPassageLinearTransport_Barrier
import Definitions.Def_FirstPassageLinearTransport_Envelope
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real BigOperators
noncomputable section

theorem FirstPassageLinearTransport.orbit_lower_of_fixed_barrier {n k : ℕ} {h t : ℝ}
    (hn : 0 < n)
    (hS : (k : ℝ) / 2 - h ≤ (oddCount n k : ℝ))
    (hphase : (3 : ℝ) ^ h ≤ (n : ℝ) ^ t) :
    centralOrbitScale k * (n : ℝ) ^ (1 - t) ≤ (orbit k n : ℝ) := by sorry

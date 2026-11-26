-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_orbit_upper_of_fixed_barrier
-- name    : FirstPassageLinearTransport.orbit_upper_of_fixed_barrier
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:01:46.424102+00:00
-- url     : https://prove2.me/theorems/60621516-6c27-521c-b612-2682f636a50d
-- title:
--   First Passage Linear Transport: orbit upper of fixed barrier
-- statement:
--   The First Passage Linear Transport construction uses the orbit upper of fixed barrier property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Envelope.lean#L484-L538
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Envelope.lean#L484-L538

import Mathlib.Algebra.Ring.GeomSum
import Definitions.Def_FirstPassageLinearTransport_Barrier
import Definitions.Def_FirstPassageLinearTransport_Envelope
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real BigOperators
noncomputable section

theorem FirstPassageLinearTransport.orbit_upper_of_fixed_barrier {n k : ℕ} {h t C : ℝ}
    (hn : 0 < n)
    (hS : (oddCount n k : ℝ) ≤ (k : ℝ) / 2 + h)
    (hphase : 2 * (3 : ℝ) ^ h ≤ (n : ℝ) ^ t)
    (hcorr : normalizedCorrection k n * (3 : ℝ) ^ ((k : ℝ) / 2) ≤
      C * (3 : ℝ) ^ h)
    (hcorrAbsorb :
      2 * (C * (3 : ℝ) ^ h * (3 : ℝ) ^ h) ≤
        centralOrbitScale k * (n : ℝ) ^ (1 + t)) :
    (orbit k n : ℝ) ≤ centralOrbitScale k * (n : ℝ) ^ (1 + t) := by sorry

-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_stoppedUpperMass_mean_lower
-- name    : FirstPassageLinearTransport.stoppedUpperMass_mean_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:30:55.233183+00:00
-- url     : https://prove2.me/theorems/cdccf46f-1c26-4bec-bb99-d656bc86c98c
-- title:
--   First Passage Linear Transport: stopped Upper Mass mean lower
-- statement:
--   The First Passage Linear Transport construction uses the stopped Upper Mass mean lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L249-L300
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L249-L300

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.stoppedUpperMass_mean_lower
    {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    {x : Bool → ℝ} (hx : ∀ b, |x b| ≤ 1) {lo hi : ℝ}
    (hlohi : lo ≤ hi) :
    ∀ r z, lo - 1 ≤ z →
      (lo - 1) * (1 - stoppedUpperMass p x lo hi r z) +
          hi * stoppedUpperMass p x lo hi r z ≤
        stoppedWalkMean p x lo hi r z := by sorry

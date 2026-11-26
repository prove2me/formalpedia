-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_orbit_lower_by_halving
-- name    : FirstPassageLinearTransport.orbit_lower_by_halving
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:33:25.664842+00:00
-- url     : https://prove2.me/theorems/770557d6-2a5c-5394-bdba-4d48f5cc5bc1
-- title:
--   First Passage Linear Transport: orbit lower by halving
-- statement:
--   The First Passage Linear Transport construction uses the orbit lower by halving property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ReciprocalHeightObstruction.lean#L177-L186
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ReciprocalHeightObstruction.lean#L177-L186

import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
import Definitions.Def_FirstPassageLinearTransport_ReciprocalHeightObstruction
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.orbit_lower_by_halving (n j : ℕ) :
    (n : ℝ) / (2 : ℝ) ^ j ≤ (orbit j n : ℝ) := by sorry

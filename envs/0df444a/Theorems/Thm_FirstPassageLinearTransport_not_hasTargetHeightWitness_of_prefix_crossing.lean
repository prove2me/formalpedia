-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_not_hasTargetHeightWitness_of_prefix_crossing
-- name    : FirstPassageLinearTransport.not_hasTargetHeightWitness_of_prefix_crossing
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:54:30.246127+00:00
-- url     : https://prove2.me/theorems/75692b89-9619-4bb6-9860-58bd8e744a33
-- title:
--   First Passage Linear Transport: not has Target Height Witness of prefix crossing
-- statement:
--   The First Passage Linear Transport construction uses the not has Target Height Witness of prefix crossing property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ReciprocalHeightObstruction.lean#L361-L389
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ReciprocalHeightObstruction.lean#L361-L389

import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
import Definitions.Def_FirstPassageLinearTransport_ReciprocalHeightObstruction
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.not_hasTargetHeightWitness_of_prefix_crossing
    {h n : ℕ} {u : ℝ} {f : ℕ → ℝ}
    (hn : 0 < n)
    (htarget : f n < (n : ℝ) / (2 : ℝ) ^ h)
    (hcross : crossesMultiplicativeFrom u h 1 (boolParityWord h n)) :
    ¬HasTargetHeightWitness f u n := by sorry

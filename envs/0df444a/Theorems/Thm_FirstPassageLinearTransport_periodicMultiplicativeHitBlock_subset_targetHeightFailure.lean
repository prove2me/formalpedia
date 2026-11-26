-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_periodicMultiplicativeHitBlock_subset_targetHeightFailure
-- name    : FirstPassageLinearTransport.periodicMultiplicativeHitBlock_subset_targetHeightFailure
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:54:38.629116+00:00
-- url     : https://prove2.me/theorems/49f08db2-200c-4153-b974-992f0374fd34
-- title:
--   First Passage Linear Transport: periodic Multiplicative Hit Block subset target Height Failure
-- statement:
--   The First Passage Linear Transport construction uses the periodic Multiplicative Hit Block subset target Height Failure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ReciprocalHeightObstruction.lean#L391-L407
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ReciprocalHeightObstruction.lean#L391-L407

import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
import Definitions.Def_FirstPassageLinearTransport_ReciprocalHeightObstruction
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.periodicMultiplicativeHitBlock_subset_targetHeightFailure
    {N t h X : ℕ} (hN : 1 ≤ N) (hblocks : t * 2 ^ h ≤ X)
    {u : ℝ} {f : ℕ → ℝ}
    (htarget : ∀ n : ℕ, N ≤ n →
      f n < (n : ℝ) / (2 : ℝ) ^ h) :
    periodicMultiplicativeHitBlock N t h u ⊆
      targetHeightFailureFinset f u X := by sorry

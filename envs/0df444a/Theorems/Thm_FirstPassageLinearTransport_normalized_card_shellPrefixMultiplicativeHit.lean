-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_normalized_card_shellPrefixMultiplicativeHit
-- name    : FirstPassageLinearTransport.normalized_card_shellPrefixMultiplicativeHit
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:54:17.439186+00:00
-- url     : https://prove2.me/theorems/888e9ed0-412a-4125-bce0-cf64750b72d2
-- title:
--   First Passage Linear Transport: normalized card shell Prefix Multiplicative Hit
-- statement:
--   The First Passage Linear Transport construction uses the normalized card shell Prefix Multiplicative Hit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ReciprocalHeightObstruction.lean#L233-L246
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ReciprocalHeightObstruction.lean#L233-L246

import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
import Definitions.Def_FirstPassageLinearTransport_ReciprocalHeightObstruction
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.normalized_card_shellPrefixMultiplicativeHit
    (M h : ℕ) (hhM : h ≤ M) (u : ℝ) :
    ((shellPrefixMultiplicativeHit M h hhM u).card : ℝ) /
        (2 : ℝ) ^ M =
      (multiplicativeHitCount u h 1 : ℝ) / (2 : ℝ) ^ h := by sorry

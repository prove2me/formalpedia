-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_frame_val
-- name    : Formalism.CountingSumsFrames.frame_val
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:23:23.673142+00:00
-- url     : https://prove2.me/theorems/a9a95a80-b07d-44dc-83ad-8b768e6a30c7
-- title:
--   Counting Sums Frames: frame val
-- statement:
--   The Counting Sums Frames construction uses the frame val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/FockGaussComparisonHolds.lean#L127-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/FockGaussComparisonHolds.lean#L127-L140

import Definitions.Def_Formalism_PolynomialDimension_FrameSum
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_FockGaussComparisonHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Finset
open Formalism Formalism.CountingSumsFrames

theorem Formalism.CountingSumsFrames.frame_val (p : ℕ) [Fact p.Prime] (D : ℕ) {r : ℕ} (m : Fin r → ℕ) (hm : ∑ i, m i ≤ D) :
    padicValNat p (D.choose (∑ i, m i) * Nat.multinomial univ m) ≤ (r + 1) * Nat.log p D := by sorry

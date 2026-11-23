-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_digit_one_letter
-- name    : Formalism.CountingSumsFrames.digit_one_letter
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:43:28.628368+00:00
-- url     : https://prove2.me/theorems/5422a086-31bf-4569-a0e9-7c1ded717032
-- title:
--   Counting Sums Frames: digit one letter
-- statement:
--   The Counting Sums Frames construction uses the digit one letter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SegmentBoundThreeHolds.lean#L35-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SegmentBoundThreeHolds.lean#L35-L49

import Definitions.Def_Formalism_PolynomialDimension_DigitSumValuationBound
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SegmentBoundThreeHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.CountingSumsFrames

theorem Formalism.CountingSumsFrames.digit_one_letter (P m t : ℕ) (hP : 0 < P) :
    ((univ : Finset (Fin (m+1) → Fin P)).filter (fun f => (∑ c, (f c : ℕ)) % P = t % P)).card = P ^ m := by sorry

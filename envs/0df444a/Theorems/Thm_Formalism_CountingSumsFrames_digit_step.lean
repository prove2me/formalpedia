-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_digit_step
-- name    : Formalism.CountingSumsFrames.digit_step
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:43:08.380792+00:00
-- url     : https://prove2.me/theorems/8f09feed-d024-4784-986b-ef852fba9cd9
-- title:
--   Counting Sums Frames: digit step
-- statement:
--   The Counting Sums Frames construction uses the digit step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/HockeyStickIdentity.lean#L78-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/HockeyStickIdentity.lean#L78-L134

import Definitions.Def_Formalism_PolynomialDimension_DigitClassSize
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HockeyStickIdentity
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

theorem Formalism.CountingSumsFrames.digit_step (P g e : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (hkey : ∀ j : ℕ, (1 - t) * ((g : ℝ) + j + 1) ≤ (P : ℝ) * ((e : ℝ) + j + 1)) :
    ∀ j : ℕ, (1 - (j : ℝ) * t) * ((g + j).choose j : ℝ) ≤ (P : ℝ) ^ j * ((e + j).choose j : ℝ) := by sorry

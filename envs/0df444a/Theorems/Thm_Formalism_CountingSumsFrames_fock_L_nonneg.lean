-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_fock_L_nonneg
-- name    : Formalism.CountingSumsFrames.fock_L_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:41:22.82582+00:00
-- url     : https://prove2.me/theorems/8b5eecae-0ca5-4aab-8cf9-0eea2ed92eb3
-- title:
--   Counting Sums Frames: fock L nonneg
-- statement:
--   The Counting Sums Frames construction uses the fock L nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/FockGaussComparisonHolds.lean#L40-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/FockGaussComparisonHolds.lean#L40-L47

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

theorem Formalism.CountingSumsFrames.fock_L_nonneg (p : ℕ) [hp : Fact p.Prime] (k : ℕ) (a : ℝ) (ha : 0 ≤ a) (hk : 1 ≤ k) :
    0 ≤ Real.logb p (2 * a + k) + 1 := by sorry

-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_sum_update_swap
-- name    : Formalism.CountingSumsFrames.sum_update_swap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:53:38.944322+00:00
-- url     : https://prove2.me/theorems/b7809cb2-c4b1-436e-935c-233027c4ca28
-- title:
--   Counting Sums Frames: sum update swap
-- statement:
--   The Counting Sums Frames construction uses the sum update swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SegmentBoundThreeHolds.lean#L144-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SegmentBoundThreeHolds.lean#L144-L171

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

theorem Formalism.CountingSumsFrames.sum_update_swap {s : ℕ} (As : Fin s → Finset ℕ) (i : Fin s) (g : (Fin s → ℕ) → ℝ) :
    ∑ aa ∈ Fintype.piFinset As, ∑ x ∈ As i, g (Function.update aa i x) =
      ((As i).card : ℝ) * ∑ aa ∈ Fintype.piFinset As, g aa := by sorry

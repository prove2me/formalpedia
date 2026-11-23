-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_one_sub_sum_mul_prod_le_prod
-- name    : Formalism.CountingSumsFrames.one_sub_sum_mul_prod_le_prod
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:50:47.916943+00:00
-- url     : https://prove2.me/theorems/021f1518-aba7-4313-a3b7-2fb4bc607d25
-- title:
--   Counting Sums Frames: one sub sum mul prod le prod
-- statement:
--   The Counting Sums Frames construction uses the one sub sum mul prod le prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/DvdPowOfNotPowSuccDvd.lean#L10-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/DvdPowOfNotPowSuccDvd.lean#L10-L28

import Definitions.Def_Formalism_PolynomialDimension_EdgeSumGoodRank
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_DvdPowOfNotPowSuccDvd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators TensorProduct
open Finset
open Formalism Formalism.CountingSumsFrames

theorem Formalism.CountingSumsFrames.one_sub_sum_mul_prod_le_prod {ι : Type} (s : Finset ι) (κ n d : ι → ℝ) (hκ : ∀ j, 0 ≤ κ j ∧ κ j ≤ 1)
    (hd : ∀ j, 0 ≤ d j) (h : ∀ j, (1 - κ j) * d j ≤ n j) :
    (1 - ∑ j ∈ s, κ j) * ∏ j ∈ s, d j ≤ ∏ j ∈ s, n j := by sorry

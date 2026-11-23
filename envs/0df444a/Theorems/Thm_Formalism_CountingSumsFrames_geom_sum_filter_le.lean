-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_geom_sum_filter_le
-- name    : Formalism.CountingSumsFrames.geom_sum_filter_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:47:02.481812+00:00
-- url     : https://prove2.me/theorems/f4d25110-d707-4421-be6e-0dc3bc426a01
-- title:
--   Counting Sums Frames: geom sum filter le
-- statement:
--   The Counting Sums Frames construction uses the geom sum filter le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SegmentHypOfIntervalHyp.lean#L171-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SegmentHypOfIntervalHyp.lean#L171-L196

import Definitions.Def_Formalism_PolynomialDimension_DigitSumValuationBound
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SegmentHypOfIntervalHyp
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

theorem Formalism.CountingSumsFrames.geom_sum_filter_le {s : ℕ} (i : Fin s) (q : ℝ) (hq0 : 0 ≤ q) :
    (1 - q) * ∑ l ∈ univ.filter (fun l : Fin s => l ≤ i), q ^ ((i:ℕ) - (l:ℕ)) ≤ 1 ∨ 1 < q := by sorry

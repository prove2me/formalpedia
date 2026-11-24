-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_Y_min_eq
-- name    : Formalism.CountingSumsFrames.Y_min_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:40:21.766338+00:00
-- url     : https://prove2.me/theorems/a403e194-a9f6-4270-81ae-d461e3e5a8e2
-- title:
--   Counting Sums Frames: Y min eq
-- statement:
--   The Counting Sums Frames construction uses the Y min eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L1666-L1675
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L1666-L1675

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_MonoCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames
open MvPolynomial Finset Formalism.GM.DimensionMonotonicity Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
variable [NeZero N] (LL : Letters N) (T : TieData) (hadm : T.Admissible LL) (i : Fin T.t)
include hadm

theorem Formalism.CountingSumsFrames.Y_min_eq [NeZero r] (LK : Letters (T.pos i + 1)) :
    Y p (r := r) LK (fun k => min (T.J k) (T.pos i + 1)) (T.thrUpTo i) = Y p LK T.J (T.thrUpTo i) := by sorry

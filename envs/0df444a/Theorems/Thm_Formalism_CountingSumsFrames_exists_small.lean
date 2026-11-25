-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_exists_small
-- name    : Formalism.CountingSumsFrames.exists_small
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:40:46.238463+00:00
-- url     : https://prove2.me/theorems/727c5c55-838c-456c-88cb-a8995b3a66a9
-- title:
--   Counting Sums Frames: exists small
-- statement:
--   The Counting Sums Frames construction uses the exists small property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L1653-L1664
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L1653-L1664

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

theorem Formalism.CountingSumsFrames.exists_small (n : Fin T.t → ℕ) {v : MvPolynomial (Fin N × Fin r) ℚ_[p]}
    (hv : v ∈ Pol p r (Lz (LL.setTies T n) (T.pos i + 1 + 1))) :
    ∃ v', rename (fun x : Fin (T.pos i + 1 + 1) × Fin r => (ιF N (T.pos i + 1) x.1, x.2)) v' = v := by sorry

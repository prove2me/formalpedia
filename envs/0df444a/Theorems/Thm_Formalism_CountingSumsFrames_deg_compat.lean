-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_deg_compat
-- name    : Formalism.CountingSumsFrames.deg_compat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:40:33.408803+00:00
-- url     : https://prove2.me/theorems/c6ce7cad-db97-47a2-92f4-1b4e26b4813d
-- title:
--   Counting Sums Frames: deg compat
-- statement:
--   The Counting Sums Frames construction uses the deg compat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L1613-L1628
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L1613-L1628

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

theorem Formalism.CountingSumsFrames.deg_compat (n : Fin T.t → ℕ) (a : Fin (T.pos i + 1 + 1)) :
    (((LL.setTies T n).takeD (T.pos i + 1)).snoc (n i)).deg a = (LL.setTies T n).deg (ιF N (T.pos i + 1) a) := by sorry

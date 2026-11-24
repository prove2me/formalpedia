-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_midAct_eq
-- name    : Formalism.CountingSumsFrames.midAct_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:36:37.894822+00:00
-- url     : https://prove2.me/theorems/859d1ff0-b91e-4b5b-b680-39f36d36f08d
-- title:
--   Counting Sums Frames: mid Act eq
-- statement:
--   The Counting Sums Frames construction uses the mid Act eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L815-L817
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L815-L817

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

theorem Formalism.CountingSumsFrames.midAct_eq (L : Letters N) {j0 J : ℕ} (hJ : j0 ≤ J) (c d : Fin r) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    midAct p L j0 J c d x = glAct p L J c d x - glAct p L j0 c d x := by sorry

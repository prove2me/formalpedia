-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_midAct_isF
-- name    : Formalism.CountingSumsFrames.midAct_isF
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:41:00.33739+00:00
-- url     : https://prove2.me/theorems/920fe238-34c4-4735-a6c8-246083aecc8b
-- title:
--   Counting Sums Frames: mid Act is F
-- statement:
--   The Counting Sums Frames construction uses the mid Act is F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L701-L710
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L701-L710

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

theorem Formalism.CountingSumsFrames.midAct_isF (L : Letters N) (j0 J : ℕ) (c d : Fin r) {g : MvPolynomial (Fin N × Fin r) ℚ_[p]}
    (hg : IsF (fsj N r j0) g) : midAct p L j0 J c d g = 0 := by sorry

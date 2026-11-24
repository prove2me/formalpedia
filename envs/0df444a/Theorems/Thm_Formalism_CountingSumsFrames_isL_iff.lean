-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_isL_iff
-- name    : Formalism.CountingSumsFrames.isL_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:36:10.687806+00:00
-- url     : https://prove2.me/theorems/ab635aba-9d55-416b-ac65-b574ff9293b3
-- title:
--   Counting Sums Frames: is L iff
-- statement:
--   The Counting Sums Frames construction uses the is L iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L676-L689
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L676-L689

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

theorem Formalism.CountingSumsFrames.isL_iff (j0 : ℕ) (g : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    IsL (fsj N r j0) g ↔ g ∈ weightedHomogeneousSubmodule ℚ_[p] (wfir N r j0) 0 := by sorry

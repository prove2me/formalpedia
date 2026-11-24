-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_isF_iff
-- name    : Formalism.CountingSumsFrames.isF_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:41:04.218801+00:00
-- url     : https://prove2.me/theorems/f9eb404d-9f9e-41bb-aeaf-e7d1bc3d7eb0
-- title:
--   Counting Sums Frames: is F iff
-- statement:
--   The Counting Sums Frames construction uses the is F iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L661-L674
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L661-L674

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

theorem Formalism.CountingSumsFrames.isF_iff (j0 : ℕ) (g : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    IsF (fsj N r j0) g ↔ g ∈ weightedHomogeneousSubmodule ℚ_[p] (wlat N r j0) 0 := by sorry

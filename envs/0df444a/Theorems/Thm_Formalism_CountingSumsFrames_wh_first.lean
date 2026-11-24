-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_wh_first
-- name    : Formalism.CountingSumsFrames.wh_first
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:45:25.576936+00:00
-- url     : https://prove2.me/theorems/96816853-2aa6-4bdc-bdeb-ee131bfe1417
-- title:
--   Counting Sums Frames: wh first
-- statement:
--   The Counting Sums Frames construction uses the wh first property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L856-L862
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L856-L862

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

theorem Formalism.CountingSumsFrames.wh_first (L : Letters N) {j0 J : ℕ} (hJ : j0 ≤ J) {ν : Fin r → ℤ} {y : MvPolynomial (Fin N × Fin r) ℚ_[p]}
    (hF : IsF (fsj N r j0) y) (hy : y ∈ weightedHomogeneousSubmodule ℚ_[p] (wv L j0) ν) :
    y ∈ weightedHomogeneousSubmodule ℚ_[p] (wv L J) ν := by sorry

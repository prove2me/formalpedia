-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_isF_of_polLz
-- name    : Formalism.CountingSumsFrames.isF_of_polLz
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:34:45.335016+00:00
-- url     : https://prove2.me/theorems/24fe52e4-760d-41d2-ad9f-05d1ea3ec15c
-- title:
--   Counting Sums Frames: is F of pol Lz
-- statement:
--   The Counting Sums Frames construction uses the is F of pol Lz property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L787-L796
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L787-L796

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

theorem Formalism.CountingSumsFrames.isF_of_polLz (L : Letters N) (j0 : ℕ) {y : MvPolynomial (Fin N × Fin r) ℚ_[p]}
    (hy : y ∈ Pol p r (Lz L j0)) : IsF (fsj N r j0) y := by sorry

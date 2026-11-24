-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_polynomial_finite_weights
-- name    : Formalism.CountingSumsFrames.polynomial_finite_weights
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:34:43.675235+00:00
-- url     : https://prove2.me/theorems/62884575-62ed-4016-be8e-b6ede67931af
-- title:
--   Counting Sums Frames: polynomial finite weights
-- statement:
--   The Counting Sums Frames construction uses the polynomial finite weights property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L1039-L1040
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L1039-L1040

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

theorem Formalism.CountingSumsFrames.polynomial_finite_weights (L : Letters N) (j0 : ℕ) : (GA p L j0).FinW (Pol p r (Lz L j0)) := by sorry

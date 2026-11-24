-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_isL_monomial_of
-- name    : Formalism.CountingSumsFrames.isL_monomial_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:40:55.487208+00:00
-- url     : https://prove2.me/theorems/80e1b5a4-3faa-4cc3-a09c-ff862f4de937
-- title:
--   Counting Sums Frames: is L monomial of
-- statement:
--   The Counting Sums Frames construction uses the is L monomial of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L1152-L1158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L1152-L1158

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

theorem Formalism.CountingSumsFrames.isL_monomial_of (j0 : ℕ) (b : Fin N × Fin r →₀ ℕ) (hb : ∀ v : Fin N × Fin r, (v.1 : ℕ) < j0 → b v = 0) (a : ℚ_[p]) :
    IsL (fsj N r j0) (monomial b a) := by sorry

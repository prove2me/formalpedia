-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_finrank_of_proj
-- name    : Formalism.CountingSumsFrames.finrank_of_proj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:40:41.0985+00:00
-- url     : https://prove2.me/theorems/b72a6310-4ce2-487e-a994-a3ed5ff039dc
-- title:
--   Counting Sums Frames: finrank of proj
-- statement:
--   The Counting Sums Frames construction uses the finrank of proj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L1094-L1123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L1094-L1123

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

theorem Formalism.CountingSumsFrames.finrank_of_proj {K V : Type} [Field K] [AddCommGroup V] [Module K V] (Y : Submodule K V)
    [FiniteDimensional K Y] {ι : Type} [Fintype ι] [DecidableEq ι] (Q : ι → Submodule K V) (P : ι → V →ₗ[K] V)
    (hQY : ∀ i, Q i ≤ Y) (c1 : ∀ i, ∀ x ∈ Y, P i x ∈ Q i) (c2 : ∀ i, ∀ x ∈ Q i, P i x = x)
    (c3 : ∀ i j, i ≠ j → ∀ x ∈ Q j, P i x = 0) (c4 : ∀ x ∈ Y, ∑ i, P i x = x) :
    Module.finrank K Y = ∑ i, Module.finrank K (Q i) := by sorry

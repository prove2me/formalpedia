-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_proj_sum
-- name    : Formalism.CountingSumsFrames.proj_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:45:32.468231+00:00
-- url     : https://prove2.me/theorems/3d9129f4-3e47-4cc0-b015-3c865b69ec16
-- title:
--   Counting Sums Frames: proj sum
-- statement:
--   The Counting Sums Frames construction uses the proj sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L427-L444
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L427-L444

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
open Formalism.GM.DimensionMonotonicity Finset
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

theorem Formalism.CountingSumsFrames.proj_sum {W : Submodule K V} {ι : Type*} [Fintype ι] (R : ι → Submodule K V) (hWR : W ≤ ⨆ i, R i)
    (π : ι → V →ₗ[K] V) (h2 : ∀ i, ∀ x ∈ R i, π i x = x) (h3 : ∀ i j, j ≠ i → ∀ x ∈ R j, π i x = 0) :
    ∀ x ∈ W, ∑ i, π i x = x := by sorry

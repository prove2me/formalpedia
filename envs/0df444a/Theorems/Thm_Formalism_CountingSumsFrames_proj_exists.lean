-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_proj_exists
-- name    : Formalism.CountingSumsFrames.proj_exists
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:36:22.365851+00:00
-- url     : https://prove2.me/theorems/1302c038-aa87-4335-84a9-9543ed27c67c
-- title:
--   Counting Sums Frames: proj exists
-- statement:
--   The Counting Sums Frames construction uses the proj exists property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L393-L425
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L393-L425

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

theorem Formalism.CountingSumsFrames.proj_exists {W : Submodule K V} {ι : Type*} [DecidableEq ι] (R : ι → Submodule K V)
    (hind : iSupIndep R) (hRW : ∀ i, R i ≤ W) (hWR : W ≤ ⨆ i, R i) :
    ∃ π : ι → V →ₗ[K] V, (∀ i x, π i x ∈ R i) ∧ (∀ i, ∀ x ∈ R i, π i x = x) ∧
      (∀ i j, j ≠ i → ∀ x ∈ R j, π i x = 0) := by sorry

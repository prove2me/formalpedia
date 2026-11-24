-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_TO_proj_exists
-- name    : Formalism.CountingSumsFrames.TO.proj_exists
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:39:47.927869+00:00
-- url     : https://prove2.me/theorems/cd5c2f2e-fe1d-4f6c-8d91-1389eb6eb871
-- title:
--   TO: proj exists
-- statement:
--   The TO construction uses the proj exists property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L414-L446
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L414-L446

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames Formalism.CountingSumsFrames.TO
open Formalism.GM.DimensionMonotonicity Finset
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

theorem Formalism.CountingSumsFrames.TO.proj_exists {W : Submodule K V} {ι : Type*} [DecidableEq ι] (R : ι → Submodule K V)
    (hind : iSupIndep R) (hRW : ∀ i, R i ≤ W) (hWR : W ≤ ⨆ i, R i) :
    ∃ π : ι → V →ₗ[K] V, (∀ i x, π i x ∈ R i) ∧ (∀ i, ∀ x ∈ R i, π i x = x) ∧
      (∀ i j, j ≠ i → ∀ x ∈ R j, π i x = 0) := by sorry

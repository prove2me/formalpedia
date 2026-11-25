-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_TO_proj_comm
-- name    : Formalism.CountingSumsFrames.TO.proj_comm
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:23:32.721806+00:00
-- url     : https://prove2.me/theorems/ebfbeccd-6740-4d6f-9cf6-1fdb56ff7759
-- title:
--   TO: proj comm
-- statement:
--   The TO construction uses the proj comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L448-L460
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L448-L460

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

theorem Formalism.CountingSumsFrames.TO.proj_comm {W : Submodule K V} {ι : Type*} (R : ι → Submodule K V) (hWR : W ≤ ⨆ i, R i)
    (π : ι → V →ₗ[K] V) (h2 : ∀ i, ∀ x ∈ R i, π i x = x) (h3 : ∀ i j, j ≠ i → ∀ x ∈ R j, π i x = 0)
    (A : V →ₗ[K] V) (hA : ∀ j, ∀ x ∈ R j, A x ∈ R j) : ∀ i, ∀ x ∈ W, π i (A x) = A (π i x) := by sorry

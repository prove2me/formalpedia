-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_TO_int_smul_mem
-- name    : Formalism.CountingSumsFrames.TO.int_smul_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:35:24.83882+00:00
-- url     : https://prove2.me/theorems/e2110556-2401-4d96-9408-72011ca14f0e
-- title:
--   TO: int smul mem
-- statement:
--   The TO construction uses the int smul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L2888-L2894
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L2888-L2894

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
open Formalism.GM Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime]

theorem Formalism.CountingSumsFrames.TO.int_smul_mem {σ : Type} (S : Submodule ℤ_[p] (MvPolynomial σ ℚ_[p])) (c : ℚ_[p]) (hc : ‖c‖ ≤ 1)
    (x : MvPolynomial σ ℚ_[p]) (hx : x ∈ S) : c • x ∈ S := by sorry

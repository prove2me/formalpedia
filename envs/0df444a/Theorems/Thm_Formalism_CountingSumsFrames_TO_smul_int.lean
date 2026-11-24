-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_TO_smul_int
-- name    : Formalism.CountingSumsFrames.TO.smul_int
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:36:24.951871+00:00
-- url     : https://prove2.me/theorems/4dcc1791-de57-494d-b6f9-2a6c0e27338b
-- title:
--   TO: smul int
-- statement:
--   The TO construction uses the smul int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L3045-L3046
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L3045-L3046

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
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.DimensionMonotonicity MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

theorem Formalism.CountingSumsFrames.TO.smul_int {σ : Type} {c : ℚ_[p]} (hc : ‖c‖ ≤ 1) {x : MvPolynomial σ ℚ_[p]} (hx : x ∈ IntPol p σ) :
    c • x ∈ IntPol p σ := by sorry

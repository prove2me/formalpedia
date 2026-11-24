-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_TO_wh_first
-- name    : Formalism.CountingSumsFrames.TO.wh_first
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:40:25.234414+00:00
-- url     : https://prove2.me/theorems/7ac3a733-648f-43df-9fb3-263a7f59a1df
-- title:
--   TO: wh first
-- statement:
--   The TO construction uses the wh first property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L899-L905
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L899-L905

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
open MvPolynomial Finset Formalism.GM.DimensionMonotonicity Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

theorem Formalism.CountingSumsFrames.TO.wh_first (L : Letters N) {j0 J : ℕ} (hJ : j0 ≤ J) {ν : Fin r → ℤ} {y : MvPolynomial (Fin N × Fin r) ℚ_[p]}
    (hF : IsF (fsj N r j0) y) (hy : y ∈ weightedHomogeneousSubmodule ℚ_[p] (wv L j0) ν) :
    y ∈ weightedHomogeneousSubmodule ℚ_[p] (wv L J) ν := by sorry

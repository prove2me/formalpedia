-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_TO_slc_wh
-- name    : Formalism.CountingSumsFrames.TO.slc_wh
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:36:24.091224+00:00
-- url     : https://prove2.me/theorems/94ce822d-5b53-4f7e-88e0-4ee209c2ef14
-- title:
--   TO: slc wh
-- statement:
--   The TO construction uses the slc wh property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L768-L784
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L768-L784

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

theorem Formalism.CountingSumsFrames.TO.slc_wh (L : Letters N) {j0 J : ℕ} (hJ : J ≤ j0) (m : Fin N × Fin r →₀ ℕ) {ν : Fin r → ℤ}
    {x : MvPolynomial (Fin N × Fin r) ℚ_[p]} (hx : x ∈ weightedHomogeneousSubmodule ℚ_[p] (wv L J) ν) :
    slc (fsj N r j0) m x ∈ weightedHomogeneousSubmodule ℚ_[p] (wv L J) ν := by sorry

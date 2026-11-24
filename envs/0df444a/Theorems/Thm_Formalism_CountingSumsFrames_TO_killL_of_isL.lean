-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_TO_killL_of_isL
-- name    : Formalism.CountingSumsFrames.TO.killL_of_isL
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:33:20.588296+00:00
-- url     : https://prove2.me/theorems/b7a78870-7208-4b9c-a5f7-e6cc5ea97af9
-- title:
--   TO: kill L of is L
-- statement:
--   The TO construction uses the kill L of is L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L743-L747
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L743-L747

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

theorem Formalism.CountingSumsFrames.TO.killL_of_isL {j0 J : ℕ} (hJ : J ≤ j0) {q : MvPolynomial (Fin N × Fin r) ℚ_[p]} (hq : IsL (fsj N r j0) q) :
    ∀ m ∈ q.support, ∀ v : Fin N × Fin r, (v.1 : ℕ) < J → m v = 0 := by sorry

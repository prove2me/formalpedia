-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_TO_isF_of_polLz
-- name    : Formalism.CountingSumsFrames.TO.isF_of_polLz
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:33:37.748822+00:00
-- url     : https://prove2.me/theorems/dda5e3ee-0136-4687-a88e-2d83698c303b
-- title:
--   TO: is F of pol Lz
-- statement:
--   The TO construction uses the is F of pol Lz property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L821-L833
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L821-L833

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

theorem Formalism.CountingSumsFrames.TO.isF_of_polLz (L : Letters N) (j0 : ℕ) {y : MvPolynomial (Fin N × Fin r) ℚ_[p]}
    (hy : y ∈ Pol p r (Lz L j0)) : IsF (fsj N r j0) y := by sorry

-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_TO_slc_ycond
-- name    : Formalism.CountingSumsFrames.TO.slc_ycond
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:40:07.967785+00:00
-- url     : https://prove2.me/theorems/aee51da6-6f2b-4272-9cd7-0b24d45f8010
-- title:
--   TO: slc ycond
-- statement:
--   The TO construction uses the slc ycond property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L794-L796
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L794-L796

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

theorem Formalism.CountingSumsFrames.TO.slc_ycond [NeZero r] (L : Letters N) {j0 J : ℕ} (hJ : J ≤ j0) (M : WithTop ℤ) (m : Fin N × Fin r →₀ ℕ)
    {F : MvPolynomial (Fin N × Fin r) ℚ_[p]} (hF : F ∈ YCond p L J M) : slc (fsj N r j0) m F ∈ YCond p L J M := by sorry

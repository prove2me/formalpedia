-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_TO_glAct_isL
-- name    : Formalism.CountingSumsFrames.TO.glAct_isL
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:38:46.400943+00:00
-- url     : https://prove2.me/theorems/abf38b78-b6bc-47d6-b8d0-e6eb8393ead8
-- title:
--   TO: gl Act is L
-- statement:
--   The TO construction uses the gl Act is L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L727-L730
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L727-L730

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

theorem Formalism.CountingSumsFrames.TO.glAct_isL (L : Letters N) (j0 J : ℕ) (c d : Fin r) {g : MvPolynomial (Fin N × Fin r) ℚ_[p]}
    (hg : IsL (fsj N r j0) g) : IsL (fsj N r j0) (glAct p L J c d g) := by sorry

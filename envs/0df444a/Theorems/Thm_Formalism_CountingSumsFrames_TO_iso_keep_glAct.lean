-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_TO_iso_keep_glAct
-- name    : Formalism.CountingSumsFrames.TO.iso_keep_glAct
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:39:25.550805+00:00
-- url     : https://prove2.me/theorems/3a27ab62-b875-4b9b-b750-473bafd01f78
-- title:
--   TO: iso keep gl Act
-- statement:
--   The TO construction uses the iso keep gl Act property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L1820-L1825
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L1820-L1825

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
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

theorem Formalism.CountingSumsFrames.TO.iso_keep_glAct (L : Letters N) {j j0 : ℕ} (hj : j ≤ j0) (c d : Fin r) (la : Fin r → ℤ) :
    ∀ x ∈ IsoC p L j univ la, glAct p L j0 c d x ∈ IsoC p L j univ la := by sorry

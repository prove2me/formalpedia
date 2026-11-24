-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_TO_glAct_X_int
-- name    : Formalism.CountingSumsFrames.TO.glAct_X_int
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:39:11.237106+00:00
-- url     : https://prove2.me/theorems/10ea9931-e508-4a76-b30d-912710f6b185
-- title:
--   TO: gl Act X int
-- statement:
--   The TO construction uses the gl Act X int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L1997-L2006
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L1997-L2006

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

theorem Formalism.CountingSumsFrames.TO.glAct_X_int (L : Letters N) (j : ℕ) (c d : Fin r) (v : Fin N × Fin r) :
    glAct p L j c d (X v) ∈ IntPol p (Fin N × Fin r) := by sorry

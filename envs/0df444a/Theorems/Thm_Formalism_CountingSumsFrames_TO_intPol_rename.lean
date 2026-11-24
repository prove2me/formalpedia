-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_TO_intPol_rename
-- name    : Formalism.CountingSumsFrames.TO.intPol_rename
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:38:50.436157+00:00
-- url     : https://prove2.me/theorems/4d695245-7b9e-4d24-9fcf-0d11279cc629
-- title:
--   TO: int Pol rename
-- statement:
--   The TO construction uses the int Pol rename property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L2181-L2185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L2181-L2185

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
open Formalism.GM Formalism.GM.M Formalism.GM.DimensionMonotonicity Formalism.GM.TM MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

theorem Formalism.CountingSumsFrames.TO.intPol_rename {σ τ : Type} (e : σ → τ) {y : MvPolynomial σ ℚ_[p]} (hy : y ∈ IntPol p σ) :
    rename e y ∈ IntPol p τ := by sorry

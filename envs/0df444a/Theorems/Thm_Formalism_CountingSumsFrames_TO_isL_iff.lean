-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_TO_isL_iff
-- name    : Formalism.CountingSumsFrames.TO.isL_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:35:46.888499+00:00
-- url     : https://prove2.me/theorems/c9809c39-1753-41a9-928b-4a4c63417cfb
-- title:
--   TO: is L iff
-- statement:
--   The TO construction uses the is L iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L704-L720
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L704-L720

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

theorem Formalism.CountingSumsFrames.TO.isL_iff (j0 : ℕ) (g : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    IsL (fsj N r j0) g ↔ g ∈ weightedHomogeneousSubmodule ℚ_[p] (wfir N r j0) 0 := by sorry

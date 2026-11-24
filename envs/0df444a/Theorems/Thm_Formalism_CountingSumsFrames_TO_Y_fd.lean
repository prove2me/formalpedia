-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_TO_Y_fd
-- name    : Formalism.CountingSumsFrames.TO.Y_fd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:35:15.30346+00:00
-- url     : https://prove2.me/theorems/1777e245-8812-458f-96c6-71a4d30b8a45
-- title:
--   TO: Y fd
-- statement:
--   The TO construction uses the Y fd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L2712-L2715
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L2712-L2715

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

theorem Formalism.CountingSumsFrames.TO.Y_fd [NeZero r] (L : Letters N) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) :
    FiniteDimensional ℚ_[p] (Y p (r := r) L J M) := by sorry

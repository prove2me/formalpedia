-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_TO_whc_comm
-- name    : Formalism.CountingSumsFrames.TO.whc_comm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:40:27.493954+00:00
-- url     : https://prove2.me/theorems/c09e3015-6f67-491b-a64d-61618cc0a520
-- title:
--   TO: whc comm
-- statement:
--   The TO construction uses the whc comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L1018-L1031
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L1018-L1031

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

theorem Formalism.CountingSumsFrames.TO.whc_comm {σ M : Type} [AddCommMonoid M] (w : σ → M) (A : MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial σ ℚ_[p])
    (hA : ∀ D x, x ∈ weightedHomogeneousSubmodule ℚ_[p] w D → A x ∈ weightedHomogeneousSubmodule ℚ_[p] w D)
    (D : M) (x : MvPolynomial σ ℚ_[p]) :
    weightedHomogeneousComponent w D (A x) = A (weightedHomogeneousComponent w D x) := by sorry

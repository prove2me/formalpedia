-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_TO_int_of_mul_monomial
-- name    : Formalism.CountingSumsFrames.TO.int_of_mul_monomial
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:39:23.81375+00:00
-- url     : https://prove2.me/theorems/27e8de70-6478-4b82-ad10-29e04a638fb5
-- title:
--   TO: int of mul monomial
-- statement:
--   The TO construction uses the int of mul monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L2529-L2533
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L2529-L2533

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

theorem Formalism.CountingSumsFrames.TO.int_of_mul_monomial {σ : Type} (g : MvPolynomial σ ℚ_[p]) (m : σ →₀ ℕ)
    (h : g * monomial m 1 ∈ IntPol p σ) : g ∈ IntPol p σ := by sorry

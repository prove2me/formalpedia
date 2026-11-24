-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_TO_pow_mul_killed
-- name    : Formalism.CountingSumsFrames.TO.pow_mul_killed
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:39:43.024828+00:00
-- url     : https://prove2.me/theorems/7330bfe0-ebe7-46e4-ba08-68047bc38ccb
-- title:
--   TO: pow mul killed
-- statement:
--   The TO construction uses the pow mul killed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L1962-L1968
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L1962-L1968

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
variable {σ : Type} (A : MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial σ ℚ_[p])
  (hA : ∀ a b, A (a * b) = a * A b + b * A a)
include hA

theorem Formalism.CountingSumsFrames.TO.pow_mul_killed {u' : MvPolynomial σ ℚ_[p]} (hu' : A u' = 0) (k : ℕ) :
    ∀ f, (A ^ k) (f * u') = (A ^ k) f * u' := by sorry

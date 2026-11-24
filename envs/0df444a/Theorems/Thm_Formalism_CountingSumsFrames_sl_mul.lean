-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_sl_mul
-- name    : Formalism.CountingSumsFrames.sl_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:45:46.040535+00:00
-- url     : https://prove2.me/theorems/47d693a1-49a9-49e7-96d0-8db2c7f64e6e
-- title:
--   Counting Sums Frames: sl mul
-- statement:
--   The Counting Sums Frames construction uses the sl mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L569-L587
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L569-L587

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_MonoCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames
open MvPolynomial Finset
variable {K : Type} [Field K] {σ : Type} [DecidableEq σ] (fs : σ → Prop) [DecidablePred fs]

theorem Formalism.CountingSumsFrames.sl_mul (m : σ →₀ ℕ) {g q : MvPolynomial σ K} (hg : IsF fs g) (hq : IsL fs q) :
    slc fs m (g * q) = coeff m q • g := by sorry

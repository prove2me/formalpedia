-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_ext_mul
-- name    : Formalism.CountingSumsFrames.ext_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:36:13.424004+00:00
-- url     : https://prove2.me/theorems/60f9e2d6-ccfa-4e6b-8618-9057b1746de8
-- title:
--   Counting Sums Frames: ext mul
-- statement:
--   The Counting Sums Frames construction uses the ext mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L557-L567
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L557-L567

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

theorem Formalism.CountingSumsFrames.ext_mul (φ : MvPolynomial σ K →ₗ[K] MvPolynomial σ K) {g q : MvPolynomial σ K} (hg : IsF fs g)
    (hq : IsL fs q) : ext fs φ (g * q) = φ g * q := by sorry

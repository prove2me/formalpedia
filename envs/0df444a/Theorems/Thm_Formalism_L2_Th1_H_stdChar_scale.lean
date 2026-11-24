-- Prove2me | Theorems.Thm_Formalism_L2_Th1_H_stdChar_scale
-- name    : Formalism.L2.Th1.H.stdChar_scale
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:07:36.296446+00:00
-- url     : https://prove2.me/theorems/2243c8d1-025a-41a4-8561-d3ab08548207
-- title:
--   H: std Char scale
-- statement:
--   The H construction uses the std Char scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/ScalePairMulMulEq.lean#L56-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/ScalePairMulMulEq.lean#L56-L58

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_QuadraticSemicharactersFactAltForm
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_Th0CharMulOpUTh0HalfPeriodEq
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_ScalePairMulMulEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
open Formalism.L2.Th1.F (scalePair)

theorem Formalism.L2.Th1.H.stdChar_scale (L : PeriodPair) (c : ℂ) (hc : c ≠ 0) {n : Type*} [Fintype n] (ω₀ : ℂ) (x : n → ℂ) :
    stdChar (scalePair L c hc) (c * ω₀) (c • x) = stdChar L ω₀ x := by sorry

-- Prove2me | Theorems.Thm_Formalism_L2_Th1_H_herm_scale
-- name    : Formalism.L2.Th1.H.herm_scale
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:41:47.045135+00:00
-- url     : https://prove2.me/theorems/b9592cf8-0d72-4181-8402-1dafbfeb2422
-- title:
--   H: herm scale
-- statement:
--   The H construction uses the herm scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/ScalePairMulMulEq.lean#L16-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/ScalePairMulMulEq.lean#L16-L25

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_QuadraticSemicharactersFactAltForm
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_Th0CharMulOpUTh0HalfPeriodEq
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_ScalePairMulMulEq
import Theorems.Thm_Formalism_L2_Th1_F_Homog_herm_scale

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

theorem Formalism.L2.Th1.H.herm_scale (L : PeriodPair) (c : ℂ) (hc : c ≠ 0) (z w : ℂ) :
    Formalism.L2.Th1.F.herm (scalePair L c hc) (c * z) (c * w) = Formalism.L2.Th1.F.herm L z w := by sorry

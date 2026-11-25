-- Prove2me | Theorems.Thm_Formalism_L2_Th1_H_scalePair_mul_mul_eq
-- name    : Formalism.L2.Th1.H.scalePair_mul_mul_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:14:56.03188+00:00
-- url     : https://prove2.me/theorems/7774d105-f7e5-4638-8496-5ff4aadeec9c
-- title:
--   H: scale Pair mul mul eq
-- statement:
--   The H construction uses the scale Pair mul mul eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/ScalePairMulMulEq.lean#L27-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/ScalePairMulMulEq.lean#L27-L29

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

theorem Formalism.L2.Th1.H.scalePair_mul_mul_eq (L : PeriodPair) (c : ℂ) (hc : c ≠ 0) (z w : ℂ) :
    Formalism.L2.Th1.F.altE (scalePair L c hc) (c * z) (c * w) = Formalism.L2.Th1.F.altE L z w := by sorry

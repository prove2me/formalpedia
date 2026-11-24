-- Prove2me | Theorems.Thm_Formalism_L2_Th1_H_stdH_scale
-- name    : Formalism.L2.Th1.H.stdH_scale
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:00:19.823657+00:00
-- url     : https://prove2.me/theorems/db1faf9a-6e96-48e0-9219-f1c29dec637f
-- title:
--   H: std H scale
-- statement:
--   The H construction uses the std H scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/ScalePairMulMulEq.lean#L48-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/ScalePairMulMulEq.lean#L48-L50

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

theorem Formalism.L2.Th1.H.stdH_scale (L : PeriodPair) (c : ℂ) (hc : c ≠ 0) (n : Type*) [Fintype n] [DecidableEq n] (z w : n → ℂ) :
    stdH (scalePair L c hc) n (c • z) (c • w) = stdH L n z w := by sorry

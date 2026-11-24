-- Prove2me | Theorems.Thm_Formalism_L2_Th1_H_cayleyGaussianIntegrals_lin_fact
-- name    : Formalism.L2.Th1.H.cayleyGaussianIntegrals_lin_fact
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T09:49:04.341103+00:00
-- url     : https://prove2.me/theorems/b872f92b-f7bf-4957-9cb7-0b12d666869e
-- title:
--   H: cayley Gaussian Integrals lin fact
-- statement:
--   The H construction uses the cayley Gaussian Integrals lin fact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/Th0CharMulOpUTh0HalfPeriodEq.lean#L40-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/Th0CharMulOpUTh0HalfPeriodEq.lean#L40-L48

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_ProductThetaMem
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_QuasiPeriodConstUnique
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_QuasiPeriodConstIsogeny
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_Th0TranslateProduct
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_Th0CharMulOpUTh0HalfPeriodEq
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

theorem Formalism.L2.Th1.H.cayleyGaussianIntegrals_lin_fact (L : PeriodPair) (s t : ℝ) (a b c : ℂ) :
    Formalism.L2.Th1.F.altE L ((s : ℂ) * a + (t : ℂ) * b) c
      = s * Formalism.L2.Th1.F.altE L a c + t * Formalism.L2.Th1.F.altE L b c := by sorry

-- Prove2me | Theorems.Thm_Formalism_L2_Th1_H_cm_th0Char
-- name    : Formalism.L2.Th1.H.cm_th0Char
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:07:55.551797+00:00
-- url     : https://prove2.me/theorems/0f3374ba-5cf8-4075-8114-57559861f176
-- title:
--   H: cm th0 Char
-- statement:
--   The H construction uses the cm th0 Char property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/Th0CharMulOpUTh0HalfPeriodEq.lean#L311-L327
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/Th0CharMulOpUTh0HalfPeriodEq.lean#L311-L327

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

theorem Formalism.L2.Th1.H.cm_th0Char (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (h4 : 4 * (a : ℤ) * c = b ^ 2 + d)
    (hodd : Odd a) (h8 : d % 8 = 7) (m k : ℤ) :
    Formalism.L2.Th1.F.thetaZeroCharacter (Formalism.L2.Th1.F.cmPair a b d ha hd) (a : ℂ)
              ((m : ℂ) * (a : ℂ) + (k : ℂ) * Formalism.L2.Th1.F.cmTheta b d)
      = (-1 : ℂ) ^ (Formalism.L2.Th1.F.cmForm a b c m k) := by sorry

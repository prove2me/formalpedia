-- Prove2me | Theorems.Thm_Formalism_L2_Th1_H_th0Char_add
-- name    : Formalism.L2.Th1.H.th0Char_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:29:31.542143+00:00
-- url     : https://prove2.me/theorems/b6181e83-83e8-45ed-a378-d2249da1dc6c
-- title:
--   H: th0 Char add
-- statement:
--   The H construction uses the th0 Char add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/Th0CharMulOpUTh0HalfPeriodEq.lean#L110-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/Th0CharMulOpUTh0HalfPeriodEq.lean#L110-L118

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

theorem Formalism.L2.Th1.H.th0Char_add (L : PeriodPair) (ω₀ x y : ℂ) (hx : x ∈ L.lattice) (hy : y ∈ L.lattice) :
    Formalism.L2.Th1.F.thetaZeroCharacter L ω₀ (x + y)
      = Formalism.L2.Th1.F.thetaZeroCharacter L ω₀ x * Formalism.L2.Th1.F.thetaZeroCharacter L ω₀ y
        * Complex.exp ((Real.pi : ℂ) * Complex.I * (Formalism.L2.Th1.F.altE L x y : ℂ)) := by sorry

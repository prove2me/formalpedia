-- Prove2me | Theorems.Thm_Formalism_L2_Th1_H_th0Char_pm
-- name    : Formalism.L2.Th1.H.th0Char_pm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:29:19.22774+00:00
-- url     : https://prove2.me/theorems/fa919ecd-018d-4b14-833f-10e530664387
-- title:
--   H: th0 Char pm
-- statement:
--   The H construction uses the th0 Char pm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/Th0CharMulOpUTh0HalfPeriodEq.lean#L96-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/Th0CharMulOpUTh0HalfPeriodEq.lean#L96-L101

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

theorem Formalism.L2.Th1.H.th0Char_pm (L : PeriodPair) (ω₀ ω : ℂ) (h0 : ω₀ ∈ L.lattice) (h : ω ∈ L.lattice) :
    Formalism.L2.Th1.F.thetaZeroCharacter L ω₀ ω = 1 ∨ Formalism.L2.Th1.F.thetaZeroCharacter L ω₀ ω = -1 := by sorry

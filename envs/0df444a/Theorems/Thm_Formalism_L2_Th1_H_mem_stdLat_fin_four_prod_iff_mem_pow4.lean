-- Prove2me | Theorems.Thm_Formalism_L2_Th1_H_mem_stdLat_fin_four_prod_iff_mem_pow4
-- name    : Formalism.L2.Th1.H.mem_stdLat_fin_four_prod_iff_mem_pow4
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T07:17:53.638364+00:00
-- url     : https://prove2.me/theorems/8c0d251e-5dea-5fe6-b0fb-4e85c3662c76
-- title:
--   H: mem std Lat fin four prod iff mem pow4
-- statement:
--   The H construction uses the mem std Lat fin four prod iff mem pow4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/RelIndexNeZeroOfNsmulMem.lean#L92-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/RelIndexNeZeroOfNsmulMem.lean#L92-L97

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CommensurableK
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_RatFourSquares
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_ScalePairMulMulEq
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_RelIndexEqAbsDetReal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_RelIndexNeZeroOfNsmulMem
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

theorem Formalism.L2.Th1.H.mem_stdLat_fin_four_prod_iff_mem_pow4 (L : PeriodPair) (n : Type*) (x : Fin 4 × n → ℂ) :
    x ∈ stdLat L (Fin 4 × n) ↔ x ∈ pow4 (stdLat L n) := by sorry

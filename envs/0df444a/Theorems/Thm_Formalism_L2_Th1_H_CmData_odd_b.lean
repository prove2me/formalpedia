-- Prove2me | Theorems.Thm_Formalism_L2_Th1_H_CmData_odd_b
-- name    : Formalism.L2.Th1.H.CmData.odd_b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:15:14.592341+00:00
-- url     : https://prove2.me/theorems/09a63d82-1732-45ad-9e7a-44b7dca289f6
-- title:
--   Cm Data: odd b
-- statement:
--   The Cm Data construction uses the odd b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/StdDataCmProof.lean#L83-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/StdDataCmProof.lean#L83-L91

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_QuadraticSemicharactersFactAltForm
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_Th0CharMulOpUTh0HalfPeriodEq
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlockFirstBlockEmb
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_ScalePairMulMulEq
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_StdDataCmProof
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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H Formalism.L2.Th1.H.CmData
open Formalism.L2.Th1.H
open Formalism.L2.Th1.F (cmPair cmTheta)
variable {n : Type} [Fintype n] [DecidableEq n]

theorem Formalism.L2.Th1.H.CmData.odd_b (a : ℕ) (b c : ℤ) (d : ℕ) (h4 : 4 * (a : ℤ) * c = b ^ 2 + d) (h8 : d % 8 = 7) : Odd b := by sorry

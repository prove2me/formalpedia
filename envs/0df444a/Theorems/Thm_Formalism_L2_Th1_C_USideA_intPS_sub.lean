-- Prove2me | Theorems.Thm_Formalism_L2_Th1_C_USideA_intPS_sub
-- name    : Formalism.L2.Th1.C.USideA.intPS_sub
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:06:52.495795+00:00
-- url     : https://prove2.me/theorems/3f2aa3c4-4c71-41c1-8c6a-d26cdfa565e4
-- title:
--   USide A: int PS sub
-- statement:
--   The USide A construction uses the int PS sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/USideA.lean#L20-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/USideA.lean#L20-L22

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_VeluIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_DegreeLeOfMemAntidiagonal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_USideA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open PowerSeries
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.C
open Formalism.L2.Th1.C.USideA
variable {K : Type} [Field K] {R : Subring K}

theorem Formalism.L2.Th1.C.USideA.intPS_sub {f g : PowerSeries K} (hf : IntPS R f) (hg : IntPS R g) : IntPS R (f - g) := by sorry

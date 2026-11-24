-- Prove2me | Theorems.Thm_Formalism_L2_Th1_C_velu_x_coordinate_integral
-- name    : Formalism.L2.Th1.C.velu_x_coordinate_integral
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:49:03.376408+00:00
-- url     : https://prove2.me/theorems/42f0113c-fb69-4700-80df-90dea3cf1b4a
-- title:
--   C: velu x coordinate integral
-- statement:
--   The C construction uses the velu x coordinate integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/IntegralEndomorphismFromDatum.lean#L139-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/IntegralEndomorphismFromDatum.lean#L139-L155

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_FirstLevelFromUniversal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_SecondCoeffConsistency
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_IntegralEndomorphismFromDatum
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
open CompactOperatorsAlt

theorem Formalism.L2.Th1.C.velu_x_coordinate_integral : VeluIntegralX := by sorry

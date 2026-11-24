-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_second_gram_vanishing_of_parts
-- name    : Formalism.FourierDecayAlt.P.second_gram_vanishing_of_parts
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:01:41.176271+00:00
-- url     : https://prove2.me/theorems/7959e87c-171c-4098-a63e-34ddd28484da
-- title:
--   P: second gram vanishing of parts
-- statement:
--   The P construction uses the second gram vanishing of parts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FirstKernelPropertiesOfHypotheses.lean#L638-L641
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FirstKernelPropertiesOfHypotheses.lean#L638-L641

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open A5x6

theorem Formalism.FourierDecayAlt.P.second_gram_vanishing_of_parts : Formalism.FourierDecayAlt.A5.BlockKernelPropertiesOfSteps := by sorry

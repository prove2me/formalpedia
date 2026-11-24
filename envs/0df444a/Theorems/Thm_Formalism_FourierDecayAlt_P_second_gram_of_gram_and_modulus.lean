-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_second_gram_of_gram_and_modulus
-- name    : Formalism.FourierDecayAlt.P.second_gram_of_gram_and_modulus
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:01:49.996244+00:00
-- url     : https://prove2.me/theorems/4137ac0a-ee70-4fda-aa0b-543e99d373bb
-- title:
--   P: second gram of gram and modulus
-- statement:
--   The P construction uses the second gram of gram and modulus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FirstKernelPropertiesOfHypotheses.lean#L636-L636
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FirstKernelPropertiesOfHypotheses.lean#L636-L636

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

theorem Formalism.FourierDecayAlt.P.second_gram_of_gram_and_modulus : Formalism.FourierDecayAlt.A5.KpGram → Formalism.FourierDecayAlt.A5.ModMul → Formalism.FourierDecayAlt.A5.BlockKernelPosSemidef := by sorry

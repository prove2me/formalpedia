-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x6_mulR_eq
-- name    : Formalism.FourierDecayAlt.P.A5x6.mulR_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:44:14.614708+00:00
-- url     : https://prove2.me/theorems/d93766c3-2fe0-4581-bf95-73f8b574e714
-- title:
--   A5x6: mul R eq
-- statement:
--   The A5x6 construction uses the mul R eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FirstKernelPropertiesOfHypotheses.lean#L28-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FirstKernelPropertiesOfHypotheses.lean#L28-L37

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
open Formalism.FourierDecayAlt.P.A5x6

theorem Formalism.FourierDecayAlt.P.A5x6.mulR_eq {K : Type} [CommRing K] (R : Subring K) (d e : K) (hd : d ∈ R) (he : e ∈ R)
    (hde : d * e = 1) : mulR R d = R.toAddSubgroup := by sorry

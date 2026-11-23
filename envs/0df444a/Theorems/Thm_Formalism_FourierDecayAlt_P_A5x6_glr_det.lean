-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x6_glr_det
-- name    : Formalism.FourierDecayAlt.P.A5x6.glr_det
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:01:52.908806+00:00
-- url     : https://prove2.me/theorems/aeb2c8db-7bbe-4ca7-a084-2cad9bcf87e2
-- title:
--   A5x6: glr det
-- statement:
--   The A5x6 construction uses the glr det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FirstKernelPropertiesOfHypotheses.lean#L52-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FirstKernelPropertiesOfHypotheses.lean#L52-L56

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

theorem Formalism.FourierDecayAlt.P.A5x6.glr_det {K : Type} [CommRing K] (R : Subring K) (h : Point K) (hh : InGLR R h) :
    (pt h.1 h.2).det ∈ R ∧ (pt h.1 h.2)⁻¹.det ∈ R ∧ (pt h.1 h.2).det * (pt h.1 h.2)⁻¹.det = 1 := by sorry

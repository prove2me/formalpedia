-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x6_orbZ_det
-- name    : Formalism.FourierDecayAlt.P.A5x6.orbZ_det
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:02:51.614796+00:00
-- url     : https://prove2.me/theorems/a5f4792c-eb5c-4398-819c-50a0ba4784c0
-- title:
--   A5x6: orb Z det
-- statement:
--   The A5x6 construction uses the orb Z det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FirstKernelPropertiesOfHypotheses.lean#L398-L402
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FirstKernelPropertiesOfHypotheses.lean#L398-L402

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

theorem Formalism.FourierDecayAlt.P.A5x6.orbZ_det {K : Type} [CommRing K] (w : Point K)
    (p : lowW K w.1 w.2 × upUniG K w.1.sum) : (orbZ w p).det = (pt w.1 w.2).det := by sorry

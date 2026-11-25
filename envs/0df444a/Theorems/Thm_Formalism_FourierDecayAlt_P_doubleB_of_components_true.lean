-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_doubleB_of_components_true
-- name    : Formalism.FourierDecayAlt.P.doubleB_of_components_true
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:34:30.938355+00:00
-- url     : https://prove2.me/theorems/074e9632-2fbe-5991-8493-610b93e67a10
-- title:
--   P: double B of components true
-- statement:
--   The P construction uses the double B of components true property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BesselScaling.lean#L102-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BesselScaling.lean#L102-L107

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaBOfComponents
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BesselScaling
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem Formalism.FourierDecayAlt.P.doubleB_of_components_true : Formalism.FourierDecayAlt.B2.LemmaBDoubleFromParts := by sorry

-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_lemma_b_crude_of_parts
-- name    : Formalism.FourierDecayAlt.P.lemma_b_crude_of_parts
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:34:38.578807+00:00
-- url     : https://prove2.me/theorems/1e1e00e8-3275-486a-85b2-ca68a426e475
-- title:
--   P: lemma b crude of parts
-- statement:
--   The P construction uses the lemma b crude of parts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HaarScaling.lean#L103-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HaarScaling.lean#L103-L105

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaBOfComponents
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HaarScaling
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
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.HaarScaling

theorem Formalism.FourierDecayAlt.P.lemma_b_crude_of_parts : Formalism.FourierDecayAlt.B2.LemmaBCrudeFromParts := by sorry

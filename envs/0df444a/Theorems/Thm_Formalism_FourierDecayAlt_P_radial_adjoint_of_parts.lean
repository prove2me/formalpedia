-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_radial_adjoint_of_parts
-- name    : Formalism.FourierDecayAlt.P.radial_adjoint_of_parts
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T16:40:22.346238+00:00
-- url     : https://prove2.me/theorems/2d718cc9-a61d-40ba-b515-04f43a01ceaa
-- title:
--   P: radial adjoint of parts
-- statement:
--   The P construction uses the radial adjoint of parts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RadialAdjointOfParts.lean#L91-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RadialAdjointOfParts.lean#L91-L108

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositiveOrbitOpen
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellOrbitSet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RadialAdjointOfParts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem Formalism.FourierDecayAlt.P.radial_adjoint_of_parts : Formalism.FourierDecayAlt.P.JFxG.RadAdjOfParts := by sorry

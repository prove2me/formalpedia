-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_crude_integrability_of_parts
-- name    : Formalism.FourierDecayAlt.P.crude_integrability_of_parts
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:29:51.445845+00:00
-- url     : https://prove2.me/theorems/6a11757d-a344-4722-af74-2a41ef43c198
-- title:
--   P: crude integrability of parts
-- statement:
--   The P construction uses the crude integrability of parts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SettingConstruction.lean#L326-L328
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SettingConstruction.lean#L326-L328

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SettingConstruction
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

theorem Formalism.FourierDecayAlt.P.crude_integrability_of_parts : Formalism.FourierDecayAlt.B2.AssembleCCIntCrude := by sorry

-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_Asm_scalar_majorant_weak_threshold
-- name    : Formalism.FourierDecayAlt.P.WeakDominationMajorants.Asm.scalar_majorant_weak_threshold
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T20:21:06.469811+00:00
-- url     : https://prove2.me/theorems/a54f77bb-7b50-480a-861f-c03627b771ca
-- title:
--   Asm: scalar majorant weak threshold
-- statement:
--   The Asm construction uses the scalar majorant weak threshold property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitalMeasurabilityWeakThreshold.lean#L73-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitalMeasurabilityWeakThreshold.lean#L73-L206

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LUFactorOrbitBounds
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BesselDomainMeasurable
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SmoothWordsAll
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SandwichRhoAction
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WordIntegralScaling
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalMeasurabilityWeakThreshold
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WeakDominationMajorants Formalism.FourierDecayAlt.P.WeakDominationMajorants.Asm
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
open Formalism.FourierDecayAlt.P.WeakDominationMajorants
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem Formalism.FourierDecayAlt.P.WeakDominationMajorants.Asm.scalar_majorant_weak_threshold : Formalism.FourierDecayAlt.P.WeakThresholdClauses.NNMajW := by sorry

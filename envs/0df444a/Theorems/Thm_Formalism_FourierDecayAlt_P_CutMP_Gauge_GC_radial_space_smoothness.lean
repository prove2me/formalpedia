-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_radial_space_smoothness
-- name    : Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.radial_space_smoothness
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T06:11:58.321527+00:00
-- url     : https://prove2.me/theorems/3cd8fca0-fb4f-5e49-9d8b-b4c88b55cbbb
-- title:
--   GC: radial space smoothness
-- statement:
--   The GC construction uses the radial space smoothness property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutGCRadSpSmooth.lean#L11-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutGCRadSpSmooth.lean#L11-L56

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGaugeGRawSmooth
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCRadSpSmooth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.radial_space_smoothness : RadSpSmooth := by sorry

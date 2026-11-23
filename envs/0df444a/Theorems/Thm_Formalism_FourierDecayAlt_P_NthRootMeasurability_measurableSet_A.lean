-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_NthRootMeasurability_measurableSet_A
-- name    : Formalism.FourierDecayAlt.P.NthRootMeasurability.measurableSet_A
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:26:50.389062+00:00
-- url     : https://prove2.me/theorems/bf69c97d-7cd9-4159-92b1-06625effcecc
-- title:
--   Nth Root Measurability: measurable Set A
-- statement:
--   The Nth Root Measurability construction uses the measurable Set A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RootPushforwardDensity.lean#L25-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RootPushforwardDensity.lean#L25-L29

import Definitions.Def_Formalism_HermitianCurvature_LatticeHerglotzBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RootPushforwardDensity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Polynomial
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.NthRootMeasurability
open Formalism.FourierDecayAlt.crystallineComparison

theorem Formalism.FourierDecayAlt.P.NthRootMeasurability.measurableSet_A (s k : ℕ) : MeasurableSet (A s k) := by sorry

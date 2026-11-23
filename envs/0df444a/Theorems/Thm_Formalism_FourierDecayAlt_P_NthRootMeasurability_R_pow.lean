-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_NthRootMeasurability_R_pow
-- name    : Formalism.FourierDecayAlt.P.NthRootMeasurability.R_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:26:34.729451+00:00
-- url     : https://prove2.me/theorems/d7369729-20dc-433e-86c5-fbe397ca4b29
-- title:
--   Nth Root Measurability: R pow
-- statement:
--   The Nth Root Measurability construction uses the R pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RootPushforwardDensity.lean#L31-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RootPushforwardDensity.lean#L31-L34

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

theorem Formalism.FourierDecayAlt.P.NthRootMeasurability.R_pow (s k : ℕ) (hs : s ≠ 0) (w : ℂ) : R s k w ^ s = w := by sorry

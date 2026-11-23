-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_NthRootMeasurability_sum_roots
-- name    : Formalism.FourierDecayAlt.P.NthRootMeasurability.sum_roots
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:26:53.954367+00:00
-- url     : https://prove2.me/theorems/9428a308-8467-467f-90ef-09f1b49ff216
-- title:
--   Nth Root Measurability: sum roots
-- statement:
--   The Nth Root Measurability construction uses the sum roots property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RootPushforwardDensity.lean#L40-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RootPushforwardDensity.lean#L40-L43

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

theorem Formalism.FourierDecayAlt.P.NthRootMeasurability.sum_roots (s : ℕ) (hs : s ≠ 0) (H : ℂ → ENNReal) (w : ℂ) :
    ((nthRoots s w).map H).sum = ∑ k ∈ Finset.range s, H (R s k w) := by sorry

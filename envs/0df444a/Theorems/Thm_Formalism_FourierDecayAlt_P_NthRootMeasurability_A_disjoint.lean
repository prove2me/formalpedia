-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_NthRootMeasurability_A_disjoint
-- name    : Formalism.FourierDecayAlt.P.NthRootMeasurability.A_disjoint
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:26:22.820264+00:00
-- url     : https://prove2.me/theorems/4523ba01-4f19-487d-bd16-f7dd3c31a85c
-- title:
--   Nth Root Measurability: A disjoint
-- statement:
--   The Nth Root Measurability construction uses the A disjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RootPushforwardDensity.lean#L45-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RootPushforwardDensity.lean#L45-L60

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

theorem Formalism.FourierDecayAlt.P.NthRootMeasurability.A_disjoint (s : ℕ) (hs : s ≠ 0) :
    Set.PairwiseDisjoint (↑(Finset.range s) : Set ℕ) (A s) := by sorry

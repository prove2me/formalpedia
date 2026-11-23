-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_NthRootMeasurability_A_union
-- name    : Formalism.FourierDecayAlt.P.NthRootMeasurability.A_union
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:26:41.78883+00:00
-- url     : https://prove2.me/theorems/1fcb8c30-7c53-4c74-b3fd-fa7c8bdd7b75
-- title:
--   Nth Root Measurability: A union
-- statement:
--   The Nth Root Measurability construction uses the A union property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RootPushforwardDensity.lean#L62-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RootPushforwardDensity.lean#L62-L72

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

theorem Formalism.FourierDecayAlt.P.NthRootMeasurability.A_union (s : ℕ) (hs : s ≠ 0) : (⋃ k ∈ Finset.range s, A s k) = {0}ᶜ := by sorry

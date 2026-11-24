-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B2x1_compactConjFromUnique
-- name    : Formalism.FourierDecayAlt.P.B2x1.compactConjFromUnique
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T15:05:57.840516+00:00
-- url     : https://prove2.me/theorems/2b484f0d-7f64-4301-8334-72c5762726b1
-- title:
--   B2x1: compact Conj From Unique
-- statement:
--   The B2x1 construction uses the compact Conj From Unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConjugationContinuousOnInvertible.lean#L225-L265
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConjugationContinuousOnInvertible.lean#L225-L265

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BlochKatoDuality
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal
open Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.B Formalism.QuantumDeterminants Formalism.REAL
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x1
variable {k r : ℕ}
variable {U : Set (Mat k r)} {hU : IsClosedSubgroup U}

theorem Formalism.FourierDecayAlt.P.B2x1.compactConjFromUnique : CompactConjFromUnique := by sorry

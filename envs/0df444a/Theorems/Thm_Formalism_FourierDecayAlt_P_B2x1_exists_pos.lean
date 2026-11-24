-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B2x1_exists_pos
-- name    : Formalism.FourierDecayAlt.P.B2x1.exists_pos
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T15:06:37.270999+00:00
-- url     : https://prove2.me/theorems/29f86873-4a81-497a-9471-b77156896a54
-- title:
--   B2x1: exists pos
-- statement:
--   The B2x1 construction uses the exists pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConjugationContinuousOnInvertible.lean#L48-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConjugationContinuousOnInvertible.lean#L48-L56

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

theorem Formalism.FourierDecayAlt.P.B2x1.exists_pos {X : Type*} [TopologicalSpace X] [SigmaCompactSpace X] [MeasurableSpace X] (μ : Measure X) (h0 : μ ≠ 0) :
    ∃ K : Set X, IsCompact K ∧ μ K ≠ 0 := by sorry

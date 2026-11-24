-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_haar_push
-- name    : Formalism.FourierDecayAlt.P.B2x3.haar_push
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T14:55:08.852792+00:00
-- url     : https://prove2.me/theorems/e93d828d-260b-481c-888e-96cc169075e1
-- title:
--   B2x3: haar push
-- statement:
--   The B2x3 construction uses the haar push property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OppositeWeylSubgroupClosed.lean#L72-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OppositeWeylSubgroupClosed.lean#L72-L122

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_RealPlaceAnalysis_FinalF
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x3
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem Formalism.FourierDecayAlt.P.B2x3.haar_push {k r : ℕ} {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [MeasurableSpace Γ] [BorelSpace Γ]
    (m : Measure Γ) [m.IsMulLeftInvariant] [m.IsMulRightInvariant] [IsFiniteMeasureOnCompacts m] (hm0 : m ≠ 0)
    (φ : Γ → Mt k r) (hφ : IsClosedEmbedding φ)
    (hmul : ∀ a b : Γ, φ (a * b) = (Matrix.of (φ a) * Matrix.of (φ b) : Mat k r))
    (U : Set (Mat k r)) (hU : Set.range φ = U) : IsHaarOn U (m.map φ) := by sorry

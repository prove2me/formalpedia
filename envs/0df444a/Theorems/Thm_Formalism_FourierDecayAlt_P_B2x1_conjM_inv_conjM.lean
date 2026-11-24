-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B2x1_conjM_inv_conjM
-- name    : Formalism.FourierDecayAlt.P.B2x1.conjM_inv_conjM
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T15:57:08.323068+00:00
-- url     : https://prove2.me/theorems/5166679b-3df6-4ae7-b464-2002c334204f
-- title:
--   B2x1: conj M inv conj M
-- statement:
--   The B2x1 construction uses the conj M inv conj M property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConjugationContinuousOnInvertible.lean#L210-L213
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConjugationContinuousOnInvertible.lean#L210-L213

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

theorem Formalism.FourierDecayAlt.P.B2x1.conjM_inv_conjM (a : Mat k r) (ha : IsUnit a.det) (x : Mt k r) : conjM a⁻¹ (conjM a x) = x := by sorry

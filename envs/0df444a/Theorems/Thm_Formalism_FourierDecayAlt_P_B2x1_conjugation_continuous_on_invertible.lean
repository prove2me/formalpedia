-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B2x1_conjugation_continuous_on_invertible
-- name    : Formalism.FourierDecayAlt.P.B2x1.conjugation_continuous_on_invertible
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T15:58:19.044816+00:00
-- url     : https://prove2.me/theorems/1c71e6d5-f1c5-4ffb-aca8-c2ffa6ad6aa2
-- title:
--   B2x1: conjugation continuous on invertible
-- statement:
--   The B2x1 construction uses the conjugation continuous on invertible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConjugationContinuousOnInvertible.lean#L219-L223
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConjugationContinuousOnInvertible.lean#L219-L223

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

theorem Formalism.FourierDecayAlt.P.B2x1.conjugation_continuous_on_invertible : ContinuousOn (conj2 : Mt k r × Mt k r → Mt k r) {p | detF p.1 ≠ 0} := by sorry

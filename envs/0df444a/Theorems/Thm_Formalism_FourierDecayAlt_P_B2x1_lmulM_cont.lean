-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B2x1_lmulM_cont
-- name    : Formalism.FourierDecayAlt.P.B2x1.lmulM_cont
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T15:25:43.573659+00:00
-- url     : https://prove2.me/theorems/da16a13b-7b79-46cb-bfcc-4ac7ef227069
-- title:
--   B2x1: lmul M cont
-- statement:
--   The B2x1 construction uses the lmul M cont property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConjugationContinuousOnInvertible.lean#L31-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConjugationContinuousOnInvertible.lean#L31-L33

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

theorem Formalism.FourierDecayAlt.P.B2x1.lmulM_cont (a : Mat k r) : Continuous (lmulM a : Mt k r → Mt k r) := by sorry

-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_haar_inversion_of_uniqueness
-- name    : Formalism.FourierDecayAlt.P.haar_inversion_of_uniqueness
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:30:40.426462+00:00
-- url     : https://prove2.me/theorems/478f9dfb-4a59-5d46-bef5-79610d2cdb51
-- title:
--   P: haar inversion of uniqueness
-- statement:
--   The P construction uses the haar inversion of uniqueness property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConjugationContinuousOnInvertible.lean#L273-L273
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConjugationContinuousOnInvertible.lean#L273-L273

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P

theorem Formalism.FourierDecayAlt.P.haar_inversion_of_uniqueness : Formalism.FourierDecayAlt.B2.HaarInvFromUnique := by sorry

-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_bessel_capelli_commute_of_parts
-- name    : Formalism.FourierDecayAlt.P.bessel_capelli_commute_of_parts
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T16:36:55.105368+00:00
-- url     : https://prove2.me/theorems/00824d40-04cb-4c0b-ba65-b282bb079350
-- title:
--   P: bessel capelli commute of parts
-- statement:
--   The P construction uses the bessel capelli commute of parts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PsiNormalization.lean#L31-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PsiNormalization.lean#L31-L63

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PsiNormalization
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem Formalism.FourierDecayAlt.P.bessel_capelli_commute_of_parts : Formalism.FourierDecayAlt.JF.BesselCommutesOfParts := by sorry

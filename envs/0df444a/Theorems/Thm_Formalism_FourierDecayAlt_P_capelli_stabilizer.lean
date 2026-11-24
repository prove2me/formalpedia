-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_capelli_stabilizer
-- name    : Formalism.FourierDecayAlt.P.capelli_stabilizer
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T17:28:15.801597+00:00
-- url     : https://prove2.me/theorems/92b530f3-ba80-4228-bf5c-e1eb5de50ccb
-- title:
--   P: capelli stabilizer
-- statement:
--   The P construction uses the capelli stabilizer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HighestWeightPolynomials.lean#L142-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HighestWeightPolynomials.lean#L142-L156

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorCommutation
import Definitions.Def_Lemmata_GeneralBFactSecondTerForm_Imports
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HighestWeightPolynomials
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr HighestWeightPolynomials

theorem Formalism.FourierDecayAlt.P.capelli_stabilizer : Qr.CapStab := by sorry

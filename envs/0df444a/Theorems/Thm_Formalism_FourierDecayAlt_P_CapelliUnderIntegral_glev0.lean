-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliUnderIntegral_glev0
-- name    : Formalism.FourierDecayAlt.P.CapelliUnderIntegral.glev0
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T16:13:17.494318+00:00
-- url     : https://prove2.me/theorems/970625fa-b270-4d73-8d68-993423b12d49
-- title:
--   Capelli Under Integral: glev0
-- statement:
--   The Capelli Under Integral construction uses the glev0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CapelliUnderIntegral.lean#L15-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CapelliUnderIntegral.lean#L15-L21

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliWordSumExpansion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliUnderIntegral
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CapelliUnderIntegral
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem Formalism.FourierDecayAlt.P.CapelliUnderIntegral.glev0 {k r : ℕ} (g : Mat k r) : g ∈ Q.Glev k r 0 ↔ g ∈ GV k r := by sorry

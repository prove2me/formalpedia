-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_cvUnderInt_of
-- name    : Formalism.FourierDecayAlt.P.JFxB.cvUnderInt_of
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T17:27:06.799924+00:00
-- url     : https://prove2.me/theorems/c78d2ed7-891e-4506-8f28-e611a6a111a0
-- title:
--   JFx B: cv Under Int of
-- statement:
--   The JFx B construction uses the cv Under Int of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/JfCVUnderIntOfParts.lean#L306-L344
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/JfCVUnderIntOfParts.lean#L306-L344

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CvRhoOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JfCVUnderIntOfParts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxB
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.JFxB.cvUnderInt_of (hJ : JF.JWords) (hW : JF.CVWordSum) (hR : JF.RwRho) : JF.CVUnderInt := by sorry

-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_Psi_I
-- name    : Formalism.FourierDecayAlt.P.JFxE.Psi_I
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T18:36:12.628469+00:00
-- url     : https://prove2.me/theorems/7805c52a-030f-40d1-b5be-4c41e9972467
-- title:
--   JFx E: Psi I
-- statement:
--   The JFx E construction uses the Psi I property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Hpart2EqZeroOfInLie.lean#L118-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Hpart2EqZeroOfInLie.lean#L118-L120

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BridgeQminor
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Hpart2EqZeroOfInLie
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxE
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity Formalism.FourierDecayAlt.P.JFxB
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem Formalism.FourierDecayAlt.P.JFxE.Psi_I (D : Mat k r →L[ℝ] E) (g Z : Mat k r) : Psi D g (Complex.I • Z) = Complex.I • Psi D g Z := by sorry

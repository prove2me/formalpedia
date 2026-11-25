-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_Psi_sub
-- name    : Formalism.FourierDecayAlt.P.JFxE.Psi_sub
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:34:37.779537+00:00
-- url     : https://prove2.me/theorems/a4b40654-31bb-4be7-b6e6-2125e348a4cb
-- title:
--   JFx E: Psi sub
-- statement:
--   The JFx E construction uses the Psi sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Hpart2EqZeroOfInLie.lean#L134-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Hpart2EqZeroOfInLie.lean#L134-L135

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

theorem Formalism.FourierDecayAlt.P.JFxE.Psi_sub (D : Mat k r →L[ℝ] E) (g Z W : Mat k r) : Psi D g (Z - W) = Psi D g Z - Psi D g W := by sorry

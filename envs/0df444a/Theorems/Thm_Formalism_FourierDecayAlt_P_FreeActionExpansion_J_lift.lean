-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_FreeActionExpansion_J_lift
-- name    : Formalism.FourierDecayAlt.P.FreeActionExpansion.J_lift
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T13:58:37.739822+00:00
-- url     : https://prove2.me/theorems/ffea3b71-7da4-4897-b5be-d80dce8fe0a1
-- title:
--   Free Action Expansion: J lift
-- statement:
--   The Free Action Expansion construction uses the J lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FreeActionExpansion.lean#L12-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FreeActionExpansion.lean#L12-L18

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionUpdateSums
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FreeActionExpansion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.FreeActionExpansion
open Finset Polynomial Formalism.FourierDecayAlt.FormPairingAction Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.GramProductIdentities Formalism.FourierDecayAlt.P.CoordinateFlipUpdateSums
open scoped Matrix
variable {A S : Type} [Ring A] [Algebra ℂ A] [Fintype S] [DecidableEq S]

theorem Formalism.FourierDecayAlt.P.FreeActionExpansion.J_lift : (Formalism.YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A)) = lift0 (Formalism.YangianSpanCharacter.T.J A) := by sorry

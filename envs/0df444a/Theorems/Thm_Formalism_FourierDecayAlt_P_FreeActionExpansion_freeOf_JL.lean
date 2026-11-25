-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_FreeActionExpansion_freeOf_JL
-- name    : Formalism.FourierDecayAlt.P.FreeActionExpansion.freeOf_JL
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T13:58:18.946793+00:00
-- url     : https://prove2.me/theorems/dfc771a0-0c42-4e3f-92a0-7a1f60c3b4e0
-- title:
--   Free Action Expansion: free Of JL
-- statement:
--   The Free Action Expansion construction uses the free Of JL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FreeActionExpansion.lean#L42-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FreeActionExpansion.lean#L42-L53

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

theorem Formalism.FourierDecayAlt.P.FreeActionExpansion.freeOf_JL (a : S) : ∀ L : List (Letter ℂ S), (∀ l ∈ L, l.plus = true) →
    a ∉ L.map Letter.intersection_update_fsHerm_neg_one → FreeOf a (JL L : SlopeTestRemainingChoices S A) := by sorry

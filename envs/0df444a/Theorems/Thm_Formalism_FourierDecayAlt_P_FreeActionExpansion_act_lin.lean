-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_FreeActionExpansion_act_lin
-- name    : Formalism.FourierDecayAlt.P.FreeActionExpansion.act_lin
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T13:58:39.30396+00:00
-- url     : https://prove2.me/theorems/5ea2970d-c776-4dee-bba1-c40a13a9f026
-- title:
--   Free Action Expansion: act lin
-- statement:
--   The Free Action Expansion construction uses the act lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FreeActionExpansion.lean#L121-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FreeActionExpansion.lean#L121-L126

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
variable {A S V : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S]
  [DecidableEq S] [AddCommGroup V] [Module ℂ V] [Module A V] [IsScalarTower ℂ A V]

theorem Formalism.FourierDecayAlt.P.FreeActionExpansion.act_lin (G : SlopeTestRemainingChoices S A) (X : Ix S → V) (P b c : A) (s : ℂ) :
    act G ((P * (b + algebraMap ℂ A s * c)) • X) = act G ((P * b) • X) + s • act G ((P * c) • X) := by sorry

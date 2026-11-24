-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_FreeActionExpansion_act_ins
-- name    : Formalism.FourierDecayAlt.P.FreeActionExpansion.act_ins
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T13:58:41.547483+00:00
-- url     : https://prove2.me/theorems/10e7c1ef-9b01-4bdf-b5f5-c11b76a66551
-- title:
--   Free Action Expansion: act ins
-- statement:
--   The Free Action Expansion construction uses the act ins property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FreeActionExpansion.lean#L73-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FreeActionExpansion.lean#L73-L96

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
variable {A S V : Type} [Ring A] [Algebra ℂ A] [Fintype S] [DecidableEq S] [AddCommGroup V]
  [Module A V]

theorem Formalism.FourierDecayAlt.P.FreeActionExpansion.act_ins (a : S) (M : M2 A) (Ψ : Ix S → V) (z : Ix S) :
    act (ins a (lift0 M)) Ψ z = ∑ j, M (z a) j • Ψ (Function.update z a j) := by sorry

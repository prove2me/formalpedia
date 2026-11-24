-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_FreeActionExpansion_comm_ins_uinv
-- name    : Formalism.FourierDecayAlt.P.FreeActionExpansion.comm_ins_uinv
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T13:58:50.816269+00:00
-- url     : https://prove2.me/theorems/ed0e7133-a1ca-49e4-aeaf-0ef7ee36825f
-- title:
--   Free Action Expansion: comm ins uinv
-- statement:
--   The Free Action Expansion construction uses the comm ins uinv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FreeActionExpansion.lean#L33-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FreeActionExpansion.lean#L33-L38

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

theorem Formalism.FourierDecayAlt.P.FreeActionExpansion.comm_ins_uinv {a : S} {C : SlopeTestRemainingChoices S A} (hC : FreeOf a C) (s : ℂ) :
    Commute C (ins a (lift0 (Formalism.YangianSpanCharacter.T.Uinv (A := A) s))) := by sorry

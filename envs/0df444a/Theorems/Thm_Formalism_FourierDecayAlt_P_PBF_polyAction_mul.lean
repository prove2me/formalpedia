-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBF_polyAction_mul
-- name    : Formalism.FourierDecayAlt.P.PBF.polyAction_mul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T17:33:06.581808+00:00
-- url     : https://prove2.me/theorems/a450cc2f-8093-4f57-8d5c-8dedcbbdc58d
-- title:
--   PBF: poly Action mul
-- statement:
--   The PBF construction uses the poly Action mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PrStarFst.lean#L25-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PrStarFst.lean#L25-L29

import Definitions.Def_Formalism_HermitianCurvature_RealInputsClosedAdmissibleSettings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PrStarFst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBF
open Finset Formalism.FourierDecayAlt.Wd
variable {V : Type} [AddCommGroup V] [Module ℂ V] {S : Type} [Fintype S] [DecidableEq S]

theorem Formalism.FourierDecayAlt.P.PBF.polyAction_mul (M N : SlopeTestRemainingChoices S (Q.Pr V)) (X : Ix S → V) : actP (M * N) X = actP M (actP N X) := by sorry

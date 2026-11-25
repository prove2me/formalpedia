-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBG_prod_neg_one_sq
-- name    : Formalism.FourierDecayAlt.P.PBG.prod_neg_one_sq
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:02:53.434718+00:00
-- url     : https://prove2.me/theorems/82f52000-b270-5d54-a999-06a52082ba6e
-- title:
--   PBG: prod neg one sq
-- statement:
--   The PBG construction uses the prod neg one sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PBGHeadV.lean#L334-L338
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PBGHeadV.lean#L334-L338

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBGHead
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ActualAdjointnessFromHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBGHeadV
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBG
open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.SignAntidiagonal
variable {A : Type} [Ring A] [Algebra ℂ A] {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.PBG.prod_neg_one_sq (m : ℕ) : (∏ l : Fin m, (-1 : ℂ) ^ (l : ℕ)) * (∏ l : Fin m, (-1 : ℂ) ^ (l : ℕ)) = 1 := by sorry

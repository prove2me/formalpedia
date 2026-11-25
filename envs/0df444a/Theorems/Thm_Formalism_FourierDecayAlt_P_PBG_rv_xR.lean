-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBG_rv_xR
-- name    : Formalism.FourierDecayAlt.P.PBG.rv_xR
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:05:21.183564+00:00
-- url     : https://prove2.me/theorems/57aae5b5-3b16-4ba2-96cc-74713872629e
-- title:
--   PBG: rv x R
-- statement:
--   The PBG construction uses the rv x R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PBGHeadV.lean#L268-L270
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PBGHeadV.lean#L268-L270

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

theorem Formalism.FourierDecayAlt.P.PBG.rv_xR (m : ℕ) (hm : m ≤ r) : rv ∘ xR k r m hm = sR k r m hm := by sorry

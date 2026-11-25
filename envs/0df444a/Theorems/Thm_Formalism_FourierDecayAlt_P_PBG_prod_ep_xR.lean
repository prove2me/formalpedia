-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBG_prod_ep_xR
-- name    : Formalism.FourierDecayAlt.P.PBG.prod_ep_xR
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:34:39.301545+00:00
-- url     : https://prove2.me/theorems/e7aaca2d-e7b0-538f-8708-2530abba059e
-- title:
--   PBG: prod ep x R
-- statement:
--   The PBG construction uses the prod ep x R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PBGHeadV.lean#L329-L332
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PBGHeadV.lean#L329-L332

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

theorem Formalism.FourierDecayAlt.P.PBG.prod_ep_xR (m : ℕ) (hm : m ≤ r) :
    ∏ l : Fin m, ep (xR k r m hm l) = ∏ l : Fin m, (-1 : ℂ) ^ (l : ℕ) := by sorry

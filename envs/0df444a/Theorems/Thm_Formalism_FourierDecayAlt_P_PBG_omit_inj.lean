-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBG_omit_inj
-- name    : Formalism.FourierDecayAlt.P.PBG.omit_inj
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T20:37:49.136141+00:00
-- url     : https://prove2.me/theorems/87496a15-0f80-40f9-818f-0608e104ab2d
-- title:
--   PBG: omit inj
-- statement:
--   The PBG construction uses the omit inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PBGHead.lean#L35-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PBGHead.lean#L35-L41

import Definitions.Def_Formalism_HermitianCurvature_RealInputsClosedAdmissibleSettings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainFirstIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBGHead
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

theorem Formalism.FourierDecayAlt.P.PBG.omit_inj {k r m : ℕ} (hm : m + 1 ≤ r) :
    Function.Injective (fun l0 : Fin (m + 1) => xR k r (m + 1) hm ∘ l0.succAbove) := by sorry

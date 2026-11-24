-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_singular_dominant
-- name    : Formalism.FourierDecayAlt.P.singular_dominant
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T16:52:44.199513+00:00
-- url     : https://prove2.me/theorems/d5a90c3f-bccb-40cf-8922-2767bf7fdbb6
-- title:
--   P: singular dominant
-- statement:
--   The P construction uses the singular dominant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CommonEigenvectors.lean#L145-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CommonEigenvectors.lean#L145-L181

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CommonEigenvectors
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Qr CommonEigenvectors
attribute [local instance 100] LieRing.ofAssociativeRing

theorem Formalism.FourierDecayAlt.P.singular_dominant : Qr.SingDom := by sorry

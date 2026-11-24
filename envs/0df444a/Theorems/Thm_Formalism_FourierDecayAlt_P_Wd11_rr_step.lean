-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_rr_step
-- name    : Formalism.FourierDecayAlt.P.Wd11.rr_step
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:48:00.887631+00:00
-- url     : https://prove2.me/theorems/7850b0ef-ab0a-4bcd-9741-3288a72497dd
-- title:
--   Wd11: rr step
-- statement:
--   The Wd11 construction uses the rr step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DiagScalarCommuteTransposedRMatrix.lean#L432-L446
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DiagScalarCommuteTransposedRMatrix.lean#L432-L446

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd11
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.Wd1

theorem Formalism.FourierDecayAlt.P.Wd11.rr_step {B : Type*} [Ring B] [StarRing B] {V Vi RR TA W L R : B}
    (h1 : V * Vi = 1) (h3 : star V * RR * V = RR) (hWV : Commute W V)
    (hsRR : Commute (star W) RR) (hsV : Commute (star W) V)
    (hT : Vi * TA * V = L * TA * R) (hL : star W * L = 1) (hR : R * W = 1) :
    star (W * V) * (RR * TA) * (W * V) = RR * TA := by sorry

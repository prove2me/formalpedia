-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_TBBx2_Bp_constant_le_rpow_of_three_le
-- name    : Formalism.FourierDecayAlt.P.TBBx2.Bp.constant_le_rpow_of_three_le
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T17:55:04.992459+00:00
-- url     : https://prove2.me/theorems/99d6488d-c44e-4cb4-8620-0aefc7e5904e
-- title:
--   Bp: constant le rpow of three le
-- statement:
--   The Bp construction uses the constant le rpow of three le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TriangleInequalityAtPlace.lean#L404-L421
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TriangleInequalityAtPlace.lean#L404-L421

import Definitions.Def_Formalism_HermitianCurvature_StatementTBB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TriangleInequalityAtPlace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TBBx2 Formalism.FourierDecayAlt.P.TBBx2.Bp
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TBB MeasureTheory
open scoped ENNReal

theorem Formalism.FourierDecayAlt.P.TBBx2.Bp.constant_le_rpow_of_three_le (C₂ b : ℝ) (hC₂ : 0 < C₂) (hb : 3 ≤ b) : C₂ ≤ b ^ (max 0 (Real.log C₂ / Real.log 3)) := by sorry

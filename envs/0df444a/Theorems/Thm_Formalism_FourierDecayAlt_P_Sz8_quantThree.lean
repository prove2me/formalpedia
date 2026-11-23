-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz8_quantThree
-- name    : Formalism.FourierDecayAlt.P.Sz8.quantThree
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:37:51.38881+00:00
-- url     : https://prove2.me/theorems/40a4a40c-b148-4fb9-acbc-996f404ec5a9
-- title:
--   Sz8: quant Three
-- statement:
--   The Sz8 construction uses the quant Three property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CmRingIdempotentUnitRatioIdentity.lean#L133-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CmRingIdempotentUnitRatioIdentity.lean#L133-L149

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmRingIdempotentUnitRatioIdentity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.Sz Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.Sz8

theorem Formalism.FourierDecayAlt.P.Sz8.quantThree (x E P M sT : ℝ) (hx : 1 ≤ x) (hPE : P ^ 2 ≤ E) (hM : 0 < M)
    (hMx : M ^ 2 ≤ x) (hsT : x * E ≤ sT) :
    P ≤ Real.sqrt (sT / (M * Real.sqrt x)) := by sorry

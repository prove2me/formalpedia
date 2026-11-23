-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz8_quantOne
-- name    : Formalism.FourierDecayAlt.P.Sz8.quantOne
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:37:12.065201+00:00
-- url     : https://prove2.me/theorems/7691a658-9267-4fc7-8907-38956496aba7
-- title:
--   Sz8: quant One
-- statement:
--   The Sz8 construction uses the quant One property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CmRingIdempotentUnitRatioIdentity.lean#L79-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CmRingIdempotentUnitRatioIdentity.lean#L79-L109

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

theorem Formalism.FourierDecayAlt.P.Sz8.quantOne (x fr mr K P W Del : ℝ) (hx : 1 ≤ x) (hm : 0 < mr) (hmf : mr ≤ fr) (hf : 1 ≤ fr)
    (hPK : P ^ 2 ≤ K) (hW : 0 < W) (hWx : 1000 * W ^ 2 ≤ x)
    (hDel : x ^ 4 * fr ^ 4 * K ≤ Del) :
    P ≤ Real.sqrt (Del / (x * (10 * mr) ^ 3)) / W := by sorry

-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz8_sqrtTTLower
-- name    : Formalism.FourierDecayAlt.P.Sz8.sqrtTTLower
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:37:12.991239+00:00
-- url     : https://prove2.me/theorems/14d26f25-0db7-4f74-8126-bd873b95a75b
-- title:
--   Sz8: sqrt TTLower
-- statement:
--   The Sz8 construction uses the sqrt TTLower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CmRingIdempotentUnitRatioIdentity.lean#L58-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CmRingIdempotentUnitRatioIdentity.lean#L58-L77

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

theorem Formalism.FourierDecayAlt.P.Sz8.sqrtTTLower (x bb cT Cb mr TT : ℝ) (hx : 1 ≤ x) (hcT : 0 < cT) (hCb : 0 < Cb) (hm : 2 ≤ mr)
    (hbb : x ^ (Cb / 2) ≤ bb) (hTT : (bb ^ (cT * mr)) ^ 2 ≤ TT) :
    x * x ^ (cT * Cb - 1) ≤ Real.sqrt TT := by sorry

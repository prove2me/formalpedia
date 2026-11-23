-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz8_delLower
-- name    : Formalism.FourierDecayAlt.P.Sz8.delLower
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:37:15.405237+00:00
-- url     : https://prove2.me/theorems/feb48ad9-a549-4da2-af16-2115b6e0f0eb
-- title:
--   Sz8: del Lower
-- statement:
--   The Sz8 construction uses the del Lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CmRingIdempotentUnitRatioIdentity.lean#L33-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CmRingIdempotentUnitRatioIdentity.lean#L33-L56

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

theorem Formalism.FourierDecayAlt.P.Sz8.delLower (k f : ℕ) (lb CDel Del : ℝ) (hk : 1 ≤ k) (hf : 1 ≤ f) (hlb : 1 ≤ lb)
    (hC : 4 < CDel) (h : ((k : ℝ) * f * lb) ^ CDel ≤ Del) :
    (k : ℝ) ^ 4 * (f : ℝ) ^ 4 * (k : ℝ) ^ (CDel - 4) ≤ Del := by sorry

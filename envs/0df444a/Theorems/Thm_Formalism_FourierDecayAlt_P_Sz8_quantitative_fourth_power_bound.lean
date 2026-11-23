-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz8_quantitative_fourth_power_bound
-- name    : Formalism.FourierDecayAlt.P.Sz8.quantitative_fourth_power_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:37:06.219704+00:00
-- url     : https://prove2.me/theorems/06744bdc-e345-4b3b-93bb-8f62195f03eb
-- title:
--   Sz8: quantitative fourth power bound
-- statement:
--   The Sz8 construction uses the quantitative fourth power bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CmRingIdempotentUnitRatioIdentity.lean#L111-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CmRingIdempotentUnitRatioIdentity.lean#L111-L131

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

theorem Formalism.FourierDecayAlt.P.Sz8.quantitative_fourth_power_bound (x fr mr K P V s Del : ℝ) (hx : 1 ≤ x) (hm : 0 < mr) (hmf : mr ≤ fr)
    (hf : 1 ≤ fr) (hP : 0 ≤ P) (hPK : P ≤ K) (hV : 0 < V) (hVx : 40 * V ≤ x) (hs0 : 0 ≤ s)
    (hs : s ≤ x) (hDel : x ^ 4 * fr ^ 4 * K ≤ Del) :
    P * (V * s * (10 * mr)) ≤ Del / 4 := by sorry

-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_RecText_geo
-- name    : Formalism.FourierDecayAlt.P.RecText.geo
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:36:05.024069+00:00
-- url     : https://prove2.me/theorems/79621e13-511e-4a9c-82c1-91216d12d290
-- title:
--   Rec Text: geo
-- statement:
--   The Rec Text construction uses the geo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RecText.lean#L7-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RecText.lean#L7-L16

import Definitions.Def_Formalism_HermitianCurvature_Statement
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RecText
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RecText
open Finset Real

theorem Formalism.FourierDecayAlt.P.RecText.geo (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1/2) :
    ∀ i, 1 ≤ i → ∑ t ∈ Icc 2 i, a ^ (t - 1) ≤ 2 * a - 2 * a ^ i := by sorry

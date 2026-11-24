-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_norm_iteratedFDerivWithin_real_eq
-- name    : Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.norm_iteratedFDerivWithin_real_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:52:24.318583+00:00
-- url     : https://prove2.me/theorems/abd37d07-e9cc-41ca-b4d7-2f3cc164c7e1
-- title:
--   Wirtinger Integration By Parts: norm iterated FDeriv Within real eq
-- statement:
--   The Wirtinger Integration By Parts construction uses the norm iterated FDeriv Within real eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WirtingerIntegrationByParts.lean#L481-L488
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WirtingerIntegrationByParts.lean#L481-L488

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WirtingerIntegrationByParts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
open Formalism.FourierDecayAlt.G MeasureTheory

theorem Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.norm_iteratedFDerivWithin_real_eq {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] {f : E → F} {s : Set E} (hs : IsOpen s) {n : ℕ}
    (hf : ContDiffOn ℂ n f s) {x : E} (hx : x ∈ s) {j : ℕ} (hj : j ≤ n) :
    ‖iteratedFDerivWithin ℝ j f s x‖ = ‖iteratedFDerivWithin ℂ j f s x‖ := by sorry

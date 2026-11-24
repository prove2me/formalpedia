-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_Bd_clm
-- name    : Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.Bd.clm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:51:54.227+00:00
-- url     : https://prove2.me/theorems/9e352fbc-25bd-4828-b066-ce4d3eadcdf7
-- title:
--   Bd: clm
-- statement:
--   The Bd construction uses the clm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WirtingerIntegrationByParts.lean#L406-L416
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WirtingerIntegrationByParts.lean#L406-L416

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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.Bd.clm {W W' : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup W'] [NormedSpace ℝ W']
    (L : W →L[ℝ] W') {f : E → W} {s : Set E} {x : E} {n : ℕ} {A P c : ℝ}
    (hs : IsOpen s) (hx : x ∈ s) (_hP : 0 ≤ P) (hf : ContDiffOn ℝ n f s) (hL : ‖L‖ ≤ c) (bf : Bd f s x n A P) :
    Bd (fun y => L (f y)) s x n (c * A) P := by sorry

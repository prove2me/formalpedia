-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_bkb_Bd_mono
-- name    : Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.bkb_Bd_mono
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:52:09.397373+00:00
-- url     : https://prove2.me/theorems/8ee126af-d2a5-4de3-bca7-f249e8fcf228
-- title:
--   Wirtinger Integration By Parts: bkb Bd mono
-- statement:
--   The Wirtinger Integration By Parts construction uses the bkb Bd mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WirtingerIntegrationByParts.lean#L493-L496
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WirtingerIntegrationByParts.lean#L493-L496

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

theorem Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.bkb_Bd_mono {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f : E → W} {s : Set E} {x : E} {n : ℕ} {A A' P : ℝ} (hP : 0 ≤ P) (hA : A ≤ A') (b : Bd f s x n A P) :
    Bd f s x n A' P := by sorry

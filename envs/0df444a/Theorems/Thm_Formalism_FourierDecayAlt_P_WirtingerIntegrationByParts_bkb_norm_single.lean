-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_bkb_norm_single
-- name    : Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.bkb_norm_single
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:51:57.511335+00:00
-- url     : https://prove2.me/theorems/7c27ac14-ed15-4bc6-9c50-d78a4374b8cc
-- title:
--   Wirtinger Integration By Parts: bkb norm single
-- statement:
--   The Wirtinger Integration By Parts construction uses the bkb norm single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WirtingerIntegrationByParts.lean#L498-L499
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WirtingerIntegrationByParts.lean#L498-L499

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

theorem Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.bkb_norm_single {d : ℕ} (k : Fin d) : ‖(Pi.single k (1 : ℂ) : Fin d → ℂ)‖ = 1 := by sorry

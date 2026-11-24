-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_wirt_contDiff
-- name    : Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.wirt_contDiff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:52:27.66491+00:00
-- url     : https://prove2.me/theorems/49791d96-8c01-4fe6-a0b0-f688f593f92b
-- title:
--   Wirtinger Integration By Parts: wirt cont Diff
-- statement:
--   The Wirtinger Integration By Parts construction uses the wirt cont Diff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WirtingerIntegrationByParts.lean#L692-L695
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WirtingerIntegrationByParts.lean#L692-L695

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
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {d : ℕ}

theorem Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.wirt_contDiff {n : ℕ} (k : Fin d) {f : (Fin d → ℂ) → V} (hf : ContDiff ℝ (n + 1 : ℕ) f) :
    ContDiff ℝ n (wirt k f) := by sorry

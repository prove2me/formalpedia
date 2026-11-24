-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_bkb_N_pos
-- name    : Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.bkb_N_pos
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:17:49.069599+00:00
-- url     : https://prove2.me/theorems/78661aa0-8b2f-46f9-966f-c893377e1e84
-- title:
--   Wirtinger Integration By Parts: bkb N pos
-- statement:
--   The Wirtinger Integration By Parts construction uses the bkb N pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WirtingerIntegrationByParts.lean#L522-L530
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WirtingerIntegrationByParts.lean#L522-L530

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

theorem Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.bkb_N_pos {d : ℕ} {L : (Fin d → ℂ) →L[ℂ] ℂ} (hL : L ≠ 0) :
    0 < ∑ l, Complex.normSq (L (Pi.single l 1)) := by sorry

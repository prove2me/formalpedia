-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_bkb_sq_le
-- name    : Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.bkb_sq_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:36:19.773739+00:00
-- url     : https://prove2.me/theorems/7115a498-b371-42df-a172-7184239d8dda
-- title:
--   Wirtinger Integration By Parts: bkb sq le
-- statement:
--   The Wirtinger Integration By Parts construction uses the bkb sq le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WirtingerIntegrationByParts.lean#L513-L520
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WirtingerIntegrationByParts.lean#L513-L520

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

theorem Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.bkb_sq_le {d : ℕ} (L : (Fin d → ℂ) →L[ℂ] ℂ) :
    ‖L‖ ^ 2 ≤ d * ∑ l, Complex.normSq (L (Pi.single l 1)) := by sorry

-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_wirt_tsupport
-- name    : Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.wirt_tsupport
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:54:41.569952+00:00
-- url     : https://prove2.me/theorems/5f575f83-d571-47a1-8ab7-87489c9d826a
-- title:
--   Wirtinger Integration By Parts: wirt tsupport
-- statement:
--   The Wirtinger Integration By Parts construction uses the wirt tsupport property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WirtingerIntegrationByParts.lean#L697-L702
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WirtingerIntegrationByParts.lean#L697-L702

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

theorem Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.wirt_tsupport (k : Fin d) (f : (Fin d → ℂ) → V) : tsupport (wirt k f) ⊆ tsupport f := by sorry

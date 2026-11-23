-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_hol_clm_decomp
-- name    : Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.hol_clm_decomp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:36:13.969952+00:00
-- url     : https://prove2.me/theorems/b8f8c5a7-4939-46f2-8c7c-21ae09d74453
-- title:
--   Wirtinger Integration By Parts: hol clm decomp
-- statement:
--   The Wirtinger Integration By Parts construction uses the hol clm decomp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WirtingerIntegrationByParts.lean#L55-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WirtingerIntegrationByParts.lean#L55-L66

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
variable {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.hol_clm_decomp (L : (Fin d → ℂ) →L[ℂ] F) :
    L = ∑ k, (ContinuousLinearMap.proj k : (Fin d → ℂ) →L[ℂ] ℂ).smulRight (L (Pi.single k 1)) := by sorry

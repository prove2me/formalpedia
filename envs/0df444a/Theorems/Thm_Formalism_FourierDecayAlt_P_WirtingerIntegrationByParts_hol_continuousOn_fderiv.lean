-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_hol_continuousOn_fderiv
-- name    : Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.hol_continuousOn_fderiv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:52:05.698046+00:00
-- url     : https://prove2.me/theorems/ecff2dc8-4198-46a1-b7ac-28da8e53f6c5
-- title:
--   Wirtinger Integration By Parts: hol continuous On fderiv
-- statement:
--   The Wirtinger Integration By Parts construction uses the hol continuous On fderiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WirtingerIntegrationByParts.lean#L127-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WirtingerIntegrationByParts.lean#L127-L136

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

theorem Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.hol_continuousOn_fderiv {Ω : Set (Fin d → ℂ)} {g : (Fin d → ℂ) → F} (hΩ : IsOpen Ω)
    (hg : DifferentiableOn ℂ g Ω) : ContinuousOn (fderiv ℂ g) Ω := by sorry

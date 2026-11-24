-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_hol_differentiableOn_fderiv
-- name    : Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.hol_differentiableOn_fderiv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:52:03.053411+00:00
-- url     : https://prove2.me/theorems/0cc33c12-93da-4f85-9a57-eaefd7ff6209
-- title:
--   Wirtinger Integration By Parts: hol differentiable On fderiv
-- statement:
--   The Wirtinger Integration By Parts construction uses the hol differentiable On fderiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WirtingerIntegrationByParts.lean#L201-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WirtingerIntegrationByParts.lean#L201-L210

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

theorem Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.hol_differentiableOn_fderiv [CompleteSpace F] {Ω : Set (Fin d → ℂ)} {g : (Fin d → ℂ) → F}
    (hΩ : IsOpen Ω) (hg : DifferentiableOn ℂ g Ω) : DifferentiableOn ℂ (fderiv ℂ g) Ω := by sorry

-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_hol_differentiableOn_fderiv_apply
-- name    : Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.hol_differentiableOn_fderiv_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:52:17.986645+00:00
-- url     : https://prove2.me/theorems/0387407f-acef-450b-a64f-0dbefadc86b5
-- title:
--   Wirtinger Integration By Parts: hol differentiable On fderiv apply
-- statement:
--   The Wirtinger Integration By Parts construction uses the hol differentiable On fderiv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WirtingerIntegrationByParts.lean#L138-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WirtingerIntegrationByParts.lean#L138-L199

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

theorem Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.hol_differentiableOn_fderiv_apply [CompleteSpace F] {Ω : Set (Fin d → ℂ)} {g : (Fin d → ℂ) → F}
    (hΩ : IsOpen Ω) (hg : DifferentiableOn ℂ g Ω) (v : Fin d → ℂ) :
    DifferentiableOn ℂ (fun x => fderiv ℂ g x v) Ω := by sorry

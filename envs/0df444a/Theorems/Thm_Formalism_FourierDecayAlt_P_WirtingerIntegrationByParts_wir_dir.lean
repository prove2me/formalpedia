-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_wir_dir
-- name    : Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.wir_dir
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:52:20.248584+00:00
-- url     : https://prove2.me/theorems/9b6036f7-7c35-408a-8c70-dee66d15f4bd
-- title:
--   Wirtinger Integration By Parts: wir dir
-- statement:
--   The Wirtinger Integration By Parts construction uses the wir dir property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WirtingerIntegrationByParts.lean#L261-L299
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WirtingerIntegrationByParts.lean#L261-L299

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

theorem Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.wir_dir {d : ℕ} (β t : ℂ) {Ω : Set (Fin d → ℂ)} {g : (Fin d → ℂ) → ℂ} (hΩ : IsOpen Ω)
    (hg : DifferentiableOn ℂ g Ω) {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    {b : (Fin d → ℂ) → V} (hb : ContDiff ℝ 1 b) (hc : HasCompactSupport b) (hsupp : tsupport b ⊆ Ω)
    (v : Fin d → ℂ) :
    Integrable (fun x => psi β (g x / t) • fderiv ℝ b x v) (volume : Measure (Fin d → ℂ)) ∧
    Integrable (fun x => (psi β (g x / t) * (Complex.I * (((β / t * fderiv ℂ g x v).re : ℝ) : ℂ))) • b x)
      (volume : Measure (Fin d → ℂ)) ∧
    ∫ x, psi β (g x / t) • fderiv ℝ b x v =
      -∫ x, (psi β (g x / t) * (Complex.I * (((β / t * fderiv ℂ g x v).re : ℝ) : ℂ))) • b x := by sorry

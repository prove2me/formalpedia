-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_hol_radius
-- name    : Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.hol_radius
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:36:26.105844+00:00
-- url     : https://prove2.me/theorems/80ebe891-f099-4e6d-832a-31ed29dadf24
-- title:
--   Wirtinger Integration By Parts: hol radius
-- statement:
--   The Wirtinger Integration By Parts construction uses the hol radius property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WirtingerIntegrationByParts.lean#L68-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WirtingerIntegrationByParts.lean#L68-L84

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

theorem Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.hol_radius {Ω : Set (Fin d → ℂ)} (hΩ : IsOpen Ω) {x₀ : Fin d → ℂ} (hx₀ : x₀ ∈ Ω) (v : Fin d → ℂ) :
    ∃ R r : ℝ, 0 < R ∧ 0 < r ∧ Metric.closedBall x₀ R ⊆ Ω ∧
      ∀ x ∈ Metric.ball x₀ (R / 2), ∀ ζ ∈ Metric.closedBall (0 : ℂ) r, x + ζ • v ∈ Metric.closedBall x₀ R := by sorry

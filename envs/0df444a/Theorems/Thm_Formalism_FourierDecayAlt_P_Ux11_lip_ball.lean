-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux11_lip_ball
-- name    : Formalism.FourierDecayAlt.P.Ux11.lip_ball
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T18:24:22.719913+00:00
-- url     : https://prove2.me/theorems/57df9338-785a-4c3f-ab74-005d3ffb1154
-- title:
--   Ux11: lip ball
-- statement:
--   The Ux11 construction uses the lip ball property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeakToStrongSmoothnessReal.lean#L30-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeakToStrongSmoothnessReal.lean#L30-L35

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeakToStrongSmoothnessReal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Set
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux11
variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem Formalism.FourierDecayAlt.P.Ux11.lip_ball {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : X → F} {x₀ : X} {r M : ℝ}
    (hd : ∀ y ∈ Metric.ball x₀ r, DifferentiableAt ℝ f y)
    (hb : ∀ y ∈ Metric.ball x₀ r, ‖fderiv ℝ f y‖ ≤ M) {y : X} (hy : y ∈ Metric.ball x₀ r) :
    ‖f y - f x₀‖ ≤ M * ‖y - x₀‖ := by sorry

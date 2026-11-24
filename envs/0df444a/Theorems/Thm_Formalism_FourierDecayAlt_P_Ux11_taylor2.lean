-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux11_taylor2
-- name    : Formalism.FourierDecayAlt.P.Ux11.taylor2
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T18:24:36.649482+00:00
-- url     : https://prove2.me/theorems/dd174fad-bdd6-40f9-a75a-a08256565a16
-- title:
--   Ux11: taylor2
-- statement:
--   The Ux11 construction uses the taylor2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeakToStrongSmoothnessReal.lean#L37-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeakToStrongSmoothnessReal.lean#L37-L62

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

theorem Formalism.FourierDecayAlt.P.Ux11.taylor2 {f : X → E} {x₀ : X} {r M : ℝ}
    (hd : ∀ y ∈ Metric.ball x₀ r, DifferentiableAt ℝ f y)
    (hd2 : ∀ y ∈ Metric.ball x₀ r, DifferentiableAt ℝ (fderiv ℝ f) y)
    (hb : ∀ y ∈ Metric.ball x₀ r, ‖fderiv ℝ (fderiv ℝ f) y‖ ≤ M) {h : X} (hh : ‖h‖ < r) :
    ‖f (x₀ + h) - f x₀ - fderiv ℝ f x₀ h‖ ≤ M * ‖h‖ ^ 2 := by sorry

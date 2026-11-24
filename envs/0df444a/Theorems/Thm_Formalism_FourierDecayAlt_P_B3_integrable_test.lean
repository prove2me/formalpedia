-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B3_integrable_test
-- name    : Formalism.FourierDecayAlt.P.B3.integrable_test
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T14:27:28.81169+00:00
-- url     : https://prove2.me/theorems/6c656207-0211-4c42-8b15-768c6806d033
-- title:
--   B3: integrable test
-- statement:
--   The B3 construction uses the integrable test property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AeEqualityFromTestFunctions.lean#L229-L242
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AeEqualityFromTestFunctions.lean#L229-L242

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AeEqualityFromTestFunctions
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B3
open Formalism.FourierDecayAlt.B

theorem Formalism.FourierDecayAlt.P.B3.integrable_test {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {w₁ w₂ : ℝ → ℝ} (h₁ : IsTest w₁)
    (h₂ : IsTest w₂) {h : ℝ × ℝ → E} (hh : ContinuousOn h Quad) :
    Integrable (fun τ : ℝ × ℝ => (w₁ τ.1 * w₂ τ.2) • h τ) (volume.restrict Quad) := by sorry

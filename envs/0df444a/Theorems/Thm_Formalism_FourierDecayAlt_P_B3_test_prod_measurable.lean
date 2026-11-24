-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B3_test_prod_measurable
-- name    : Formalism.FourierDecayAlt.P.B3.test_prod_measurable
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T14:33:35.520129+00:00
-- url     : https://prove2.me/theorems/6d5202d1-1f3b-4b92-87a5-4c647941f72a
-- title:
--   B3: test prod measurable
-- statement:
--   The B3 construction uses the test prod measurable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AeEqualityFromTestFunctions.lean#L93-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AeEqualityFromTestFunctions.lean#L93-L96

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

theorem Formalism.FourierDecayAlt.P.B3.test_prod_measurable {w₁ w₂ : ℝ → ℝ} (h₁ : IsTest w₁) (h₂ : IsTest w₂) :
    Measurable fun τ : ℝ × ℝ => ENNReal.ofReal (w₁ τ.1 * w₂ τ.2) := by sorry

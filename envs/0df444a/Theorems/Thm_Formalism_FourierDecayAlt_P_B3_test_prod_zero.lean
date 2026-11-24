-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B3_test_prod_zero
-- name    : Formalism.FourierDecayAlt.P.B3.test_prod_zero
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T14:27:29.422801+00:00
-- url     : https://prove2.me/theorems/58dd09af-9f4d-4b00-b00e-eebbc549dea0
-- title:
--   B3: test prod zero
-- statement:
--   The B3 construction uses the test prod zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AeEqualityFromTestFunctions.lean#L86-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AeEqualityFromTestFunctions.lean#L86-L91

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

theorem Formalism.FourierDecayAlt.P.B3.test_prod_zero {w₁ w₂ : ℝ → ℝ} (h₁ : IsTest w₁) (h₂ : IsTest w₂) {τ : ℝ × ℝ} (hτ : τ ∉ Quad) :
    w₁ τ.1 * w₂ τ.2 = 0 := by sorry

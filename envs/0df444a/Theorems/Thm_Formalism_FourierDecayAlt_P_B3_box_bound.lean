-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B3_box_bound
-- name    : Formalism.FourierDecayAlt.P.B3.box_bound
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T14:29:53.27419+00:00
-- url     : https://prove2.me/theorems/ef8cd7eb-ea1b-4b6a-a6ed-80dee3bf0fc5
-- title:
--   B3: box bound
-- statement:
--   The B3 construction uses the box bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AeEqualityFromTestFunctions.lean#L102-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AeEqualityFromTestFunctions.lean#L102-L107

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

theorem Formalism.FourierDecayAlt.P.B3.box_bound (f : ℝ × ℝ → ℝ≥0∞) {a₁ b₁ a₂ b₂ : ℝ} (h₁ : 0 < a₁) (h₂ : 0 < a₂) (τ : ℝ × ℝ) :
    (Ioo a₁ b₁ ×ˢ Ioo a₂ b₂).indicator f τ ≤
      ENNReal.ofReal (pl (a₁ / 2) (b₁ + 1) (2 / a₁ + 1) τ.1 * pl (a₂ / 2) (b₂ + 1) (2 / a₂ + 1) τ.2) * f τ := by sorry

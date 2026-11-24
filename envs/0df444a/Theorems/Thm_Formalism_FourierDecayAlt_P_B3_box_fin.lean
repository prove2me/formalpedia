-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B3_box_fin
-- name    : Formalism.FourierDecayAlt.P.B3.box_fin
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T14:27:34.37649+00:00
-- url     : https://prove2.me/theorems/b79f00e4-0dd9-435a-9742-e4b3c14df264
-- title:
--   B3: box fin
-- statement:
--   The B3 construction uses the box fin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AeEqualityFromTestFunctions.lean#L116-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AeEqualityFromTestFunctions.lean#L116-L120

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

theorem Formalism.FourierDecayAlt.P.B3.box_fin {f : ℝ × ℝ → ℝ≥0∞} (hfin : FinT f) {a₁ a₂ : ℝ} (b₁ b₂ : ℝ) (h₁ : 0 < a₁) (h₂ : 0 < a₂) :
    ((volume.restrict Quad).withDensity f) (Ioo a₁ b₁ ×ˢ Ioo a₂ b₂) ≠ ∞ := by sorry

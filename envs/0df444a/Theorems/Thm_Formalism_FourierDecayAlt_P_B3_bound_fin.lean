-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B3_bound_fin
-- name    : Formalism.FourierDecayAlt.P.B3.bound_fin
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T14:28:33.860106+00:00
-- url     : https://prove2.me/theorems/c4c3e896-04fb-4fad-813a-3f2524c314ce
-- title:
--   B3: bound fin
-- statement:
--   The B3 construction uses the bound fin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AeEqualityFromTestFunctions.lean#L109-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AeEqualityFromTestFunctions.lean#L109-L114

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

theorem Formalism.FourierDecayAlt.P.B3.bound_fin {f : ℝ × ℝ → ℝ≥0∞} (hfin : FinT f) {a₁ a₂ : ℝ} (b₁ b₂ : ℝ) (h₁ : 0 < a₁) (h₂ : 0 < a₂) :
    (∫⁻ τ, ENNReal.ofReal (pl (a₁ / 2) (b₁ + 1) (2 / a₁ + 1) τ.1 * pl (a₂ / 2) (b₂ + 1) (2 / a₂ + 1) τ.2) * f τ
      ∂(volume.restrict Quad)) ≠ ∞ := by sorry

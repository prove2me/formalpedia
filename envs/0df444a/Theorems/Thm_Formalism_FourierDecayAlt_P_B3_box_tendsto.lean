-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B3_box_tendsto
-- name    : Formalism.FourierDecayAlt.P.B3.box_tendsto
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T14:29:20.158062+00:00
-- url     : https://prove2.me/theorems/87b0a5e1-08eb-478a-8dc5-65f4d8007675
-- title:
--   B3: box tendsto
-- statement:
--   The B3 construction uses the box tendsto property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AeEqualityFromTestFunctions.lean#L122-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AeEqualityFromTestFunctions.lean#L122-L155

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

theorem Formalism.FourierDecayAlt.P.B3.box_tendsto {f : ℝ × ℝ → ℝ≥0∞} (hf : AEMeasurable f (volume.restrict Quad)) (hfin : FinT f)
    {a₁ a₂ : ℝ} (b₁ b₂ : ℝ) (h₁ : 0 < a₁) (h₂ : 0 < a₂) :
    Tendsto (fun n : ℕ => ∫⁻ τ, ENNReal.ofReal (pl a₁ b₁ n τ.1 * pl a₂ b₂ n τ.2) * f τ ∂(volume.restrict Quad))
      atTop (𝓝 (((volume.restrict Quad).withDensity f) (Ioo a₁ b₁ ×ˢ Ioo a₂ b₂))) := by sorry

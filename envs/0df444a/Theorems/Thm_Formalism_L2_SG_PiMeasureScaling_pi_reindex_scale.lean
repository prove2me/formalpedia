-- Prove2me | Theorems.Thm_Formalism_L2_SG_PiMeasureScaling_pi_reindex_scale
-- name    : Formalism.L2.SG.PiMeasureScaling.pi_reindex_scale
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:13:27.021508+00:00
-- url     : https://prove2.me/theorems/99042a5f-b90d-41fe-957e-a82a0f1aa9ff
-- title:
--   Pi Measure Scaling: pi reindex scale
-- statement:
--   The Pi Measure Scaling construction uses the pi reindex scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/PiMeasureScaling.lean#L45-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/PiMeasureScaling.lean#L45-L67

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_PiMeasureScaling
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.PiMeasureScaling

theorem Formalism.L2.SG.PiMeasureScaling.pi_reindex_scale {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι ≃ κ)
    (a : ℝ≥0∞) (ha : a ≠ ⊤) (s : ι → ℂ) (hs : ∀ i, s i ≠ 0) :
    (Measure.pi (fun _ : κ => a • (volume : Measure ℂ))).map (fun y i => s i * y (e i)) =
      (∏ i, a * ENNReal.ofReal (Complex.normSq (s i))⁻¹) • (volume : Measure (ι → ℂ)) := by sorry

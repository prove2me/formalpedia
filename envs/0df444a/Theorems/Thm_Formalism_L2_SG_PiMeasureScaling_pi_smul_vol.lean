-- Prove2me | Theorems.Thm_Formalism_L2_SG_PiMeasureScaling_pi_smul_vol
-- name    : Formalism.L2.SG.PiMeasureScaling.pi_smul_vol
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:50:16.42664+00:00
-- url     : https://prove2.me/theorems/293d3c3e-81b3-43f7-9cd9-81c494927e6c
-- title:
--   Pi Measure Scaling: pi smul vol
-- statement:
--   The Pi Measure Scaling construction uses the pi smul vol property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/PiMeasureScaling.lean#L16-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/PiMeasureScaling.lean#L16-L21

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

theorem Formalism.L2.SG.PiMeasureScaling.pi_smul_vol {ι : Type*} [Fintype ι] (c : ι → ℝ≥0∞) (hc : ∀ i, c i ≠ ⊤) :
    Measure.pi (fun i => c i • (volume : Measure ℂ)) = (∏ i, c i) • (volume : Measure (ι → ℂ)) := by sorry

-- Prove2me | Theorems.Thm_Formalism_L2_SG_PiMeasureScaling_reindex_mp
-- name    : Formalism.L2.SG.PiMeasureScaling.reindex_mp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:50:20.778593+00:00
-- url     : https://prove2.me/theorems/583826c3-079f-4267-a9ad-d6f528cc9867
-- title:
--   Pi Measure Scaling: reindex mp
-- statement:
--   The Pi Measure Scaling construction uses the reindex mp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/PiMeasureScaling.lean#L34-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/PiMeasureScaling.lean#L34-L43

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

theorem Formalism.L2.SG.PiMeasureScaling.reindex_mp {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι ≃ κ) :
    MeasurePreserving (fun (y : κ → ℂ) (i : ι) => y (e i)) volume volume := by sorry

-- Prove2me | Theorems.Thm_Formalism_L2_SG_PiMeasureScaling_sf_smul
-- name    : Formalism.L2.SG.PiMeasureScaling.sf_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:05:48.040728+00:00
-- url     : https://prove2.me/theorems/94ba3c77-f6d8-4e83-995d-ef8c173d2eee
-- title:
--   Pi Measure Scaling: sf smul
-- statement:
--   The Pi Measure Scaling construction uses the sf smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/PiMeasureScaling.lean#L10-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/PiMeasureScaling.lean#L10-L14

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

theorem Formalism.L2.SG.PiMeasureScaling.sf_smul (c : ℝ≥0∞) (hc : c ≠ ⊤) : SigmaFinite (c • (volume : Measure ℂ)) := by sorry

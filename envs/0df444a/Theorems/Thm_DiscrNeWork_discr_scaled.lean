-- Prove2me | Theorems.Thm_DiscrNeWork_discr_scaled
-- name    : DiscrNeWork.discr_scaled
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:09:32.692179+00:00
-- url     : https://prove2.me/theorems/acd47d29-a494-453d-8c79-9117cdc20c6f
-- title:
--   Discr Ne Work: discr scaled
-- statement:
--   The Discr Ne Work construction uses the discr scaled property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/NonzeroDiscriminants/DiscMain.lean#L109-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/NonzeroDiscriminants/DiscMain.lean#L109-L121

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DiscrNe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NonzeroDiscriminants_DiscLat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NonzeroDiscriminants_DiscMain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ModularForm EisensteinSeries UpperHalfPlane
noncomputable section
open DiscrNeWork

theorem DiscrNeWork.discr_scaled (a : ℂ) (ha : a ≠ 0) (τ : ℍ) : PI.discr (PI.lat2 a (a * τ)) ≠ 0 := by sorry

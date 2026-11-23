-- Prove2me | Theorems.Thm_DiscrNeWork_toLat_bij
-- name    : DiscrNeWork.toLat_bij
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:09:53.253282+00:00
-- url     : https://prove2.me/theorems/86ff5253-6fe1-472a-b970-62e1a5b4c3db
-- title:
--   Discr Ne Work: to Lat bij
-- statement:
--   The Discr Ne Work construction uses the to Lat bij property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/NonzeroDiscriminants/DiscLat.lean#L50-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/NonzeroDiscriminants/DiscLat.lean#L50-L79

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DiscrNe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NonzeroDiscriminants_DiscLat
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

theorem DiscrNeWork.toLat_bij (a : ℂ) (ha : a ≠ 0) (τ : ℍ) : Function.Bijective (toLat a ha τ) := by sorry

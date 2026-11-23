-- Prove2me | Theorems.Thm_DiscrNeWork_bern6
-- name    : DiscrNeWork.bern6
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:09:35.370807+00:00
-- url     : https://prove2.me/theorems/3586b8ea-6272-4ede-92e3-a7a369aa1bd8
-- title:
--   Discr Ne Work: bern6
-- statement:
--   The Discr Ne Work construction uses the bern6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/NonzeroDiscriminants/DiscMain.lean#L11-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/NonzeroDiscriminants/DiscMain.lean#L11-L20

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

theorem DiscrNeWork.bern6 : bernoulli 6 = 1 / 42 := by sorry

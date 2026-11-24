-- Prove2me | Theorems.Thm_Formalism_GM_DimensionMonotonicity_casI_closed
-- name    : Formalism.GM.DimensionMonotonicity.casI_closed
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:46:47.890811+00:00
-- url     : https://prove2.me/theorems/901e4fb0-f8ee-4cbe-abcd-9dc999d5efe7
-- title:
--   Dimension Monotonicity: cas I closed
-- statement:
--   The Dimension Monotonicity construction uses the cas I closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L373-L388
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L373-L388

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeBij
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.DimensionMonotonicity
open Finset
variable {r : ℕ}

theorem Formalism.GM.DimensionMonotonicity.casI_closed (μ : Fin r → ℤ) : GlW.casI μ = ∑ c : Fin r, μ c * (μ c + ((r : ℤ) - 1 - 2 * (c : ℤ))) := by sorry

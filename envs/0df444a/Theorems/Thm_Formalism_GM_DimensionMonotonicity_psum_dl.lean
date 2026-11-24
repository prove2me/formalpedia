-- Prove2me | Theorems.Thm_Formalism_GM_DimensionMonotonicity_psum_dl
-- name    : Formalism.GM.DimensionMonotonicity.psum_dl
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:36:53.611809+00:00
-- url     : https://prove2.me/theorems/821b67d7-c377-4fa8-a097-5dacd739ba4e
-- title:
--   Dimension Monotonicity: psum dl
-- statement:
--   The Dimension Monotonicity construction uses the psum dl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L276-L287
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L276-L287

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

theorem Formalism.GM.DimensionMonotonicity.psum_dl (a b : Fin r) (k : ℕ) :
    psum (dl a b) k = (if (a : ℕ) < k then 1 else 0) - (if (b : ℕ) < k then 1 else 0) := by sorry

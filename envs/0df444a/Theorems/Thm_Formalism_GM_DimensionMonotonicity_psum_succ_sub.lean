-- Prove2me | Theorems.Thm_Formalism_GM_DimensionMonotonicity_psum_succ_sub
-- name    : Formalism.GM.DimensionMonotonicity.psum_succ_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:48:24.007443+00:00
-- url     : https://prove2.me/theorems/506b1513-4abf-4430-9bfb-eb61b3d7224c
-- title:
--   Dimension Monotonicity: psum succ sub
-- statement:
--   The Dimension Monotonicity construction uses the psum succ sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L261-L269
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L261-L269

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

theorem Formalism.GM.DimensionMonotonicity.psum_succ_sub (μ : Fin r → ℤ) (c : Fin r) : psum μ (c + 1) - psum μ c = μ c := by sorry

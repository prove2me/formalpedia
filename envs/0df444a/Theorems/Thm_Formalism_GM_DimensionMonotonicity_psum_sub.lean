-- Prove2me | Theorems.Thm_Formalism_GM_DimensionMonotonicity_psum_sub
-- name    : Formalism.GM.DimensionMonotonicity.psum_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:36:32.27635+00:00
-- url     : https://prove2.me/theorems/0d34f69c-b18c-4f74-b6d4-78c6c3e82912
-- title:
--   Dimension Monotonicity: psum sub
-- statement:
--   The Dimension Monotonicity construction uses the psum sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L251-L255
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L251-L255

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

theorem Formalism.GM.DimensionMonotonicity.psum_sub (μ ν : Fin r → ℤ) (k : ℕ) : psum (μ - ν) k = psum μ k - psum ν k := by sorry

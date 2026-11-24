-- Prove2me | Theorems.Thm_Formalism_GM_DimensionMonotonicity_psum_range
-- name    : Formalism.GM.DimensionMonotonicity.psum_range
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:48:38.013139+00:00
-- url     : https://prove2.me/theorems/fda083f2-2018-4f2d-b5ce-1a4004cbd6f7
-- title:
--   Dimension Monotonicity: psum range
-- statement:
--   The Dimension Monotonicity construction uses the psum range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L318-L328
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L318-L328

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

theorem Formalism.GM.DimensionMonotonicity.psum_range (g : ℕ → ℤ) {k r : ℕ} (h : k ≤ r) :
    ∑ c ∈ range r, (if c < k then g c else 0) = ∑ c ∈ range k, g c := by sorry

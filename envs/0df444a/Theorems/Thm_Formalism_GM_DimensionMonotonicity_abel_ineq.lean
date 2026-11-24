-- Prove2me | Theorems.Thm_Formalism_GM_DimensionMonotonicity_abel_ineq
-- name    : Formalism.GM.DimensionMonotonicity.abel_ineq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:46:30.024076+00:00
-- url     : https://prove2.me/theorems/2b43a69e-6844-4028-b035-2ebb8f63f3ad
-- title:
--   Dimension Monotonicity: abel ineq
-- statement:
--   The Dimension Monotonicity construction uses the abel ineq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L330-L371
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L330-L371

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

theorem Formalism.GM.DimensionMonotonicity.abel_ineq (r : ℕ) (δ t : ℕ → ℤ) (hD : ∀ k ≤ r, 0 ≤ ∑ c ∈ range k, δ c)
    (hT : ∑ c ∈ range r, δ c = 0) (ht : ∀ c, c + 1 < r → 2 ≤ t c - t (c + 1)) :
    0 ≤ ∑ c ∈ range r, t c * δ c ∧ (∑ c ∈ range r, t c * δ c = 0 → ∀ c < r, δ c = 0) := by sorry

-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_WorkedExample_sum_split_three_intervals
-- name    : Formalism.CohomologicalDescent.WorkedExample.sum_split_three_intervals
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:01:57.22285+00:00
-- url     : https://prove2.me/theorems/56563512-bad6-4e73-8781-7524cc300478
-- title:
--   Worked Example: sum split three intervals
-- statement:
--   The Worked Example construction uses the sum split three intervals property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/WorkedExample.lean#L252-L258
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/WorkedExample.lean#L252-L258

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_MultiplicityZeroThickEmbedding
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeckeLFunctionIdealEulerProduct
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WorkedExample
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.WorkedExample
open Formalism.CohomologicalDescent

theorem Formalism.CohomologicalDescent.WorkedExample.sum_split_three_intervals {N : ℕ} (f : Fin N → ℤ) (x y : ℕ) (hxy : x ≤ y) :
    ∑ a, f a = ∑ a ∈ Finset.univ.filter (fun a : Fin N => (a : ℕ) < x), f a +
      ∑ a ∈ Finset.univ.filter (fun a : Fin N => x ≤ (a : ℕ) ∧ (a : ℕ) < y), f a +
      ∑ a ∈ Finset.univ.filter (fun a : Fin N => y ≤ (a : ℕ)), f a := by sorry

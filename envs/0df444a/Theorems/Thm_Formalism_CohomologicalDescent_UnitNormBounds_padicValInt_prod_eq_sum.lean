-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_UnitNormBounds_padicValInt_prod_eq_sum
-- name    : Formalism.CohomologicalDescent.UnitNormBounds.padicValInt_prod_eq_sum
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:00:38.29383+00:00
-- url     : https://prove2.me/theorems/11ac60f6-73ea-49b8-8105-45cc2bc9364a
-- title:
--   Unit Norm Bounds: padic Val Int prod eq sum
-- statement:
--   The Unit Norm Bounds construction uses the padic Val Int prod eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/UnitNormBounds.lean#L203-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/UnitNormBounds.lean#L203-L212

import Definitions.Def_Formalism_PieriBlockIdeals_FactorialValuationSum
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LabelSumNeedsLeFalse
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_UnitNormBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.UnitNormBounds
open Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD

theorem Formalism.CohomologicalDescent.UnitNormBounds.padicValInt_prod_eq_sum (l : ℕ) [Fact l.Prime] (s : Finset ℕ) (g : ℕ → ℤ) (hg : ∀ x ∈ s, g x ≠ 0) :
    padicValInt l (∏ x ∈ s, g x) = ∑ x ∈ s, padicValInt l (g x) := by sorry

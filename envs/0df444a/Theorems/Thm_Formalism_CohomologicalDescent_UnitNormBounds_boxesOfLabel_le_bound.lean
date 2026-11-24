-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_UnitNormBounds_boxesOfLabel_le_bound
-- name    : Formalism.CohomologicalDescent.UnitNormBounds.boxesOfLabel_le_bound
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:00:39.165822+00:00
-- url     : https://prove2.me/theorems/b0ce2feb-7b8e-414e-9fde-250b840e77f7
-- title:
--   Unit Norm Bounds: boxes Of Label le bound
-- statement:
--   The Unit Norm Bounds construction uses the boxes Of Label le bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/UnitNormBounds.lean#L137-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/UnitNormBounds.lean#L137-L162

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

theorem Formalism.CohomologicalDescent.UnitNormBounds.boxesOfLabel_le_bound (k j t w M i : ℕ) (lam : Fin (k + j) → ℕ) (xm xp : ℤ) (hR : Rows k j t w M lam xm xp)
    (tau : Fin (k + j) → ℕ) (htau : tau ∈ shapes t (M - w) i (dual M lam)) (ct : ℤ) :
    (boxesOfLabel t w M lam tau ct : ℝ) ≤
      (if ct < xm then (j : ℝ) else 0) +
        min (min (k : ℝ) (t : ℝ)) (if ct < xm then (i : ℝ) / ((xm - ct : ℤ) : ℝ) else (k : ℝ)) := by sorry

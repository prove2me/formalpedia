-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_UnitNormBounds_mem_label_interval_of_mu_ne_zero
-- name    : Formalism.CohomologicalDescent.UnitNormBounds.mem_label_interval_of_mu_ne_zero
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:00:36.246666+00:00
-- url     : https://prove2.me/theorems/ef570c68-163d-464c-b0bd-805161a2c449
-- title:
--   Unit Norm Bounds: mem label interval of mu ne zero
-- statement:
--   The Unit Norm Bounds construction uses the mem label interval of mu ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/UnitNormBounds.lean#L180-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/UnitNormBounds.lean#L180-L201

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

theorem Formalism.CohomologicalDescent.UnitNormBounds.mem_label_interval_of_mu_ne_zero (k j t w M i : ℕ) (lam : Fin (k + j) → ℕ) (xm xp : ℤ) (hR : Rows k j t w M lam xm xp)
    (ct : ℤ) (hmu : mu t (M - w) i (dual M lam) (cont t w M ct) ≠ 0) : maxB t w < ct ∧ ct < xp := by sorry

-- Prove2me | Theorems.Thm_Formalism_MainNotions_MassRatioZetaBound_rpow_bounds
-- name    : Formalism.MainNotions.MassRatioZetaBound.rpow_bounds
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:42:59.772049+00:00
-- url     : https://prove2.me/theorems/1fe8a9e1-2db8-40f6-aacf-9b34a16a2022
-- title:
--   Mass Ratio Zeta Bound: rpow bounds
-- statement:
--   The Mass Ratio Zeta Bound construction uses the rpow bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/MassRatioBound.lean#L122-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/MassRatioBound.lean#L122-L136

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementMass
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_MassRatioBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.MassRatioZetaBound
open NumberField
variable {K : Type*} [Field K] [NumberField K]

theorem Formalism.MainNotions.MassRatioZetaBound.rpow_bounds {N : ℝ} (hN : 2 ≤ N) {M : ℕ} (hM : 3 ≤ M) :
    N ^ (-(M : ℝ) / 2) ≤ 1 / N ^ ((3 : ℝ) / 2) ∧ 1 / N ^ ((3 : ℝ) / 2) ≤ 1 / 2 := by sorry

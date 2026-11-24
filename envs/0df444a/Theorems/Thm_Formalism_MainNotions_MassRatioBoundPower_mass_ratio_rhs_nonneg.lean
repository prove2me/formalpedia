-- Prove2me | Theorems.Thm_Formalism_MainNotions_MassRatioBoundPower_mass_ratio_rhs_nonneg
-- name    : Formalism.MainNotions.MassRatioBoundPower.mass_ratio_rhs_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:18:16.595384+00:00
-- url     : https://prove2.me/theorems/b44bf54d-3242-46f8-9440-8d0314ddf472
-- title:
--   Mass Ratio Bound Power: mass ratio rhs nonneg
-- statement:
--   The Mass Ratio Bound Power construction uses the mass ratio rhs nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/MassRatioBoundPower.lean#L14-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/MassRatioBoundPower.lean#L14-L17

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_MassRatioBound
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_MassRatioBoundPower
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.MassRatioBoundPower
open NumberField Formalism.MainNotions.MassRatioZetaBound
variable {K : Type*} [Field K] [NumberField K]

theorem Formalism.MainNotions.MassRatioBoundPower.mass_ratio_rhs_nonneg [StarRing K] {M : ℕ} (hM : 3 ≤ M) : 0 ≤ Formalism.HermitianLatticesTheory.massRatioRightSide K M := by sorry

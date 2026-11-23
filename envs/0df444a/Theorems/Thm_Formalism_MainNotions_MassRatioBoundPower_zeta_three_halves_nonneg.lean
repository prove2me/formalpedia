-- Prove2me | Theorems.Thm_Formalism_MainNotions_MassRatioBoundPower_zeta_three_halves_nonneg
-- name    : Formalism.MainNotions.MassRatioBoundPower.zeta_three_halves_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:43:12.762648+00:00
-- url     : https://prove2.me/theorems/5e86e775-0033-4dde-975a-74e3ddbe8e38
-- title:
--   Mass Ratio Bound Power: zeta three halves nonneg
-- statement:
--   The Mass Ratio Bound Power construction uses the zeta three halves nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/MassRatioBoundPower.lean#L19-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/MassRatioBoundPower.lean#L19-L19

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

theorem Formalism.MainNotions.MassRatioBoundPower.zeta_three_halves_nonneg : 0 ≤ zetaGL3GL2 := by sorry

-- Prove2me | Theorems.Thm_Formalism_MainNotions_MassRatioBoundPower_exp_le_two_pow
-- name    : Formalism.MainNotions.MassRatioBoundPower.exp_le_two_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:17:31.804176+00:00
-- url     : https://prove2.me/theorems/acd43b4f-b0a5-44e1-8cfa-4b8c0a15ba79
-- title:
--   Mass Ratio Bound Power: exp le two pow
-- statement:
--   The Mass Ratio Bound Power construction uses the exp le two pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/MassRatioBoundPower.lean#L23-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/MassRatioBoundPower.lean#L23-L30

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

theorem Formalism.MainNotions.MassRatioBoundPower.exp_le_two_pow : Real.exp (4 * zetaGL3GL2) ≤ 2 ^ cZ := by sorry

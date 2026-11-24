-- Prove2me | Theorems.Thm_Formalism_MainNotions_MassRatioZetaBound_summable_Z
-- name    : Formalism.MainNotions.MassRatioZetaBound.summable_Z
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T09:56:50.547937+00:00
-- url     : https://prove2.me/theorems/3eb26975-a920-4111-8a77-ecac9383cefb
-- title:
--   Mass Ratio Zeta Bound: summable Z
-- statement:
--   The Mass Ratio Zeta Bound construction uses the summable Z property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/MassRatioBound.lean#L84-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/MassRatioBound.lean#L84-L85

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

theorem Formalism.MainNotions.MassRatioZetaBound.summable_Z : Summable fun m : ℕ => 1 / (m : ℝ) ^ ((3 : ℝ) / 2) := by sorry

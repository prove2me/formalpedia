-- Prove2me | Theorems.Thm_Formalism_MainNotions_N_KillingConditions_WildPf_val_intCast_le
-- name    : Formalism.MainNotions.N.KillingConditions.WildPf.val_intCast_le
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T10:03:41.952345+00:00
-- url     : https://prove2.me/theorems/e2c8a906-3e93-4294-9523-2b05dc8a7c5d
-- title:
--   Wild Pf: val int Cast le
-- statement:
--   The Wild Pf construction uses the val int Cast le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/LevelLetterCocycles/WildPro.lean#L51-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/LevelLetterCocycles/WildPro.lean#L51-L52

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactRightVersion_Imports
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_WildPro
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.KillingConditions Formalism.MainNotions.N.KillingConditions.WildPf
variable {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] (A : ValuationSubring Ω)
variable {A}

theorem Formalism.MainNotions.N.KillingConditions.WildPf.val_intCast_le (a : ℤ) : A.valuation ((a : ℤ) : Ω) ≤ 1 := by sorry

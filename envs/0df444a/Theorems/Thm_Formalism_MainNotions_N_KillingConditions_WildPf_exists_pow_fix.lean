-- Prove2me | Theorems.Thm_Formalism_MainNotions_N_KillingConditions_WildPf_exists_pow_fix
-- name    : Formalism.MainNotions.N.KillingConditions.WildPf.exists_pow_fix
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T10:03:12.846444+00:00
-- url     : https://prove2.me/theorems/85986570-cd66-4cdd-9362-278ac41dd972
-- title:
--   Wild Pf: exists pow fix
-- statement:
--   The Wild Pf construction uses the exists pow fix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/LevelLetterCocycles/WildPro.lean#L122-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/LevelLetterCocycles/WildPro.lean#L122-L123

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

theorem Formalism.MainNotions.N.KillingConditions.WildPf.exists_pow_fix (σ : Ω ≃ₐ[E] Ω) (y : Ω) (hy : IsIntegral E y) : ∃ n : ℕ, n ≠ 0 ∧ (σ ^ n) y = y := by sorry

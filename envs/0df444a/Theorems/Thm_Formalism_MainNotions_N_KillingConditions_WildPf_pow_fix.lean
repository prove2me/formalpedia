-- Prove2me | Theorems.Thm_Formalism_MainNotions_N_KillingConditions_WildPf_pow_fix
-- name    : Formalism.MainNotions.N.KillingConditions.WildPf.pow_fix
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:48:21.934584+00:00
-- url     : https://prove2.me/theorems/74bd799f-8305-4684-9d8e-325e5fefff73
-- title:
--   Wild Pf: pow fix
-- statement:
--   The Wild Pf construction uses the pow fix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/LevelLetterCocycles/WildPro.lean#L76-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/LevelLetterCocycles/WildPro.lean#L76-L79

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

theorem Formalism.MainNotions.N.KillingConditions.WildPf.pow_fix {τ : Ω ≃ₐ[E] Ω} {y : Ω} (h : τ y = y) (j : ℕ) : (τ ^ j) y = y := by sorry

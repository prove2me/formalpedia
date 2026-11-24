-- Prove2me | Theorems.Thm_Formalism_MainNotions_N_KillingConditions_WildPf_IsWild_pow
-- name    : Formalism.MainNotions.N.KillingConditions.WildPf.IsWild.pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:48:08.903115+00:00
-- url     : https://prove2.me/theorems/b46a4b1d-0399-4b07-9820-60c22350e98d
-- title:
--   Is Wild: pow
-- statement:
--   The Is Wild construction uses the pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/LevelLetterCocycles/WildPro.lean#L46-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/LevelLetterCocycles/WildPro.lean#L46-L49

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

theorem Formalism.MainNotions.N.KillingConditions.WildPf.IsWild.pow {σ : Ω ≃ₐ[E] Ω} (h : IsWild A σ) (n : ℕ) : IsWild A (σ ^ n) := by sorry

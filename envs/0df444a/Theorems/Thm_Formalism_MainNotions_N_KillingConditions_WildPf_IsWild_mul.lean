-- Prove2me | Theorems.Thm_Formalism_MainNotions_N_KillingConditions_WildPf_IsWild_mul
-- name    : Formalism.MainNotions.N.KillingConditions.WildPf.IsWild.mul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:03:16.871923+00:00
-- url     : https://prove2.me/theorems/4dca84c1-f930-40b7-a453-2941f93c5c0c
-- title:
--   Is Wild: mul
-- statement:
--   The Is Wild construction uses the mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/LevelLetterCocycles/WildPro.lean#L34-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/LevelLetterCocycles/WildPro.lean#L34-L44

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

theorem Formalism.MainNotions.N.KillingConditions.WildPf.IsWild.mul {σ τ : Ω ≃ₐ[E] Ω} (hσ : IsWild A σ) (hτ : IsWild A τ) : IsWild A (σ * τ) := by sorry

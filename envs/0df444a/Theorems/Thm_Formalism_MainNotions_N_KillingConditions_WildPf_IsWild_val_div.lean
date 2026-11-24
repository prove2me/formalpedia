-- Prove2me | Theorems.Thm_Formalism_MainNotions_N_KillingConditions_WildPf_IsWild_val_div
-- name    : Formalism.MainNotions.N.KillingConditions.WildPf.IsWild.val_div
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:03:23.149772+00:00
-- url     : https://prove2.me/theorems/7762c635-a580-4f4a-9e25-ea569ad910da
-- title:
--   Is Wild: val div
-- statement:
--   The Is Wild construction uses the val div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/LevelLetterCocycles/WildPro.lean#L30-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/LevelLetterCocycles/WildPro.lean#L30-L32

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

theorem Formalism.MainNotions.N.KillingConditions.WildPf.IsWild.val_div {σ : Ω ≃ₐ[E] Ω} (h : IsWild A σ) {y : Ω} (hy : y ≠ 0) : A.valuation (σ y / y) = 1 := by sorry

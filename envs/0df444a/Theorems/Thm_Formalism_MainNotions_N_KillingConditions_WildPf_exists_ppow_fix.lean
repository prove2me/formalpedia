-- Prove2me | Theorems.Thm_Formalism_MainNotions_N_KillingConditions_WildPf_exists_ppow_fix
-- name    : Formalism.MainNotions.N.KillingConditions.WildPf.exists_ppow_fix
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T10:03:17.686267+00:00
-- url     : https://prove2.me/theorems/5b23e199-9966-4fae-a1c8-08a7d975fe5b
-- title:
--   Wild Pf: exists ppow fix
-- statement:
--   The Wild Pf construction uses the exists ppow fix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/LevelLetterCocycles/WildPro.lean#L125-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/LevelLetterCocycles/WildPro.lean#L125-L140

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

theorem Formalism.MainNotions.N.KillingConditions.WildPf.exists_ppow_fix {p : ℕ} (hp : p.Prime) (hpA : A.valuation ((p : ℕ) : Ω) < 1) {σ : Ω ≃ₐ[E] Ω} (hσ : IsWild A σ)
    (y : Ω) (hy : IsIntegral E y) : ∃ a : ℕ, ∀ k, a ≤ k → (σ ^ (p ^ k)) y = y := by sorry

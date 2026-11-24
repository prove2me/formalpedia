-- Prove2me | Theorems.Thm_Formalism_MainNotions_N_KillingConditions_WildPf_fix_of_coprime
-- name    : Formalism.MainNotions.N.KillingConditions.WildPf.fix_of_coprime
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T10:03:30.052369+00:00
-- url     : https://prove2.me/theorems/c1489f62-3121-427d-8efb-3c8534efdfa3
-- title:
--   Wild Pf: fix of coprime
-- statement:
--   The Wild Pf construction uses the fix of coprime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/LevelLetterCocycles/WildPro.lean#L81-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/LevelLetterCocycles/WildPro.lean#L81-L120

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

theorem Formalism.MainNotions.N.KillingConditions.WildPf.fix_of_coprime {p m : ℕ} (hpA : A.valuation ((p : ℕ) : Ω) < 1) (hm : Nat.Coprime m p) {τ : Ω ≃ₐ[E] Ω}
    (hτ : IsWild A τ) (y : Ω) (hy : (τ ^ m) y = y) : τ y = y := by sorry

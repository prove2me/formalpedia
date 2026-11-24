-- Prove2me | Theorems.Thm_Formalism_MainNotions_N_KillingConditions_WildPf_val_natCast_eq_one
-- name    : Formalism.MainNotions.N.KillingConditions.WildPf.val_natCast_eq_one
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T10:03:22.536114+00:00
-- url     : https://prove2.me/theorems/89a51593-379d-4b12-a6e5-1cb7cd4bc118
-- title:
--   Wild Pf: val nat Cast eq one
-- statement:
--   The Wild Pf construction uses the val nat Cast eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/LevelLetterCocycles/WildPro.lean#L54-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/LevelLetterCocycles/WildPro.lean#L54-L74

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

theorem Formalism.MainNotions.N.KillingConditions.WildPf.val_natCast_eq_one {p m : ℕ} (hpA : A.valuation ((p : ℕ) : Ω) < 1) (hm : Nat.Coprime m p) :
    A.valuation ((m : ℕ) : Ω) = 1 := by sorry

-- Prove2me | Theorems.Thm_Formalism_WindowSums_zv_emult_eq_val
-- name    : Formalism.WindowSums.zv_emult_eq_val
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T10:39:27.044284+00:00
-- url     : https://prove2.me/theorems/a71c61f6-c593-48fe-91bb-e720597ebc4b
-- title:
--   Window Sums: zv emult eq val
-- statement:
--   The Window Sums construction uses the zv emult eq val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WindowSums/AnnihilatorPolynomials/ZpowVal.lean#L13-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WindowSums/AnnihilatorPolynomials/ZpowVal.lean#L13-L17

import Definitions.Def_Formalism_WindowSums_Statement
import Definitions.Def_Formalism_WindowSums_AnnihilatorPolynomials_ZpowVal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.WindowSums
open Finset
variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

theorem Formalism.WindowSums.zv_emult_eq_val {x : ℤ_[ℓ]} (hx : x ≠ 0) :
    emultiplicity (ℓ : ℤ_[ℓ]) x = (x.valuation : ℕ∞) := by sorry

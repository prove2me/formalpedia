-- Prove2me | Theorems.Thm_Formalism_WindowSums_zv_two_sq_step
-- name    : Formalism.WindowSums.zv_two_sq_step
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T10:39:57.497471+00:00
-- url     : https://prove2.me/theorems/50f3c2d1-6db8-4dd9-9646-7df0ff4cecde
-- title:
--   Window Sums: zv two sq step
-- statement:
--   The Window Sums construction uses the zv two sq step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WindowSums/AnnihilatorPolynomials/ZpowVal.lean#L30-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WindowSums/AnnihilatorPolynomials/ZpowVal.lean#L30-L50

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

theorem Formalism.WindowSums.zv_two_sq_step (h2 : ℓ = 2) {x : ℤ_[ℓ]} (h4 : (ℓ : ℤ_[ℓ]) ^ 2 ∣ x - 1) :
    emultiplicity (ℓ : ℤ_[ℓ]) (x ^ 2 - 1) = emultiplicity (ℓ : ℤ_[ℓ]) (x - 1) + 1 := by sorry

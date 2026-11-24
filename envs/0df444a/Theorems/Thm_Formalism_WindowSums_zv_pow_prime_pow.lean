-- Prove2me | Theorems.Thm_Formalism_WindowSums_zv_pow_prime_pow
-- name    : Formalism.WindowSums.zv_pow_prime_pow
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T10:39:50.957404+00:00
-- url     : https://prove2.me/theorems/79450ccf-0d15-4599-ba08-11333137b4c1
-- title:
--   Window Sums: zv pow prime pow
-- statement:
--   The Window Sums construction uses the zv pow prime pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WindowSums/AnnihilatorPolynomials/ZpowVal.lean#L52-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WindowSums/AnnihilatorPolynomials/ZpowVal.lean#L52-L70

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

theorem Formalism.WindowSums.zv_pow_prime_pow (x : ℤ_[ℓ]) (hx : (ℓ : ℤ_[ℓ]) ∣ x - 1)
    (h2 : ℓ = 2 → (ℓ : ℤ_[ℓ]) ^ 2 ∣ x - 1) (k : ℕ) :
    emultiplicity (ℓ : ℤ_[ℓ]) (x ^ ℓ ^ k - 1) = emultiplicity (ℓ : ℤ_[ℓ]) (x - 1) + k := by sorry

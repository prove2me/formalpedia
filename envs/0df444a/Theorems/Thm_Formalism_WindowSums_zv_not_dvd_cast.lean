-- Prove2me | Theorems.Thm_Formalism_WindowSums_zv_not_dvd_cast
-- name    : Formalism.WindowSums.zv_not_dvd_cast
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T10:39:38.693859+00:00
-- url     : https://prove2.me/theorems/4a2dc797-fd6a-45c3-b4f2-542a760130a1
-- title:
--   Window Sums: zv not dvd cast
-- statement:
--   The Window Sums construction uses the zv not dvd cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WindowSums/AnnihilatorPolynomials/ZpowVal.lean#L72-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WindowSums/AnnihilatorPolynomials/ZpowVal.lean#L72-L78

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

theorem Formalism.WindowSums.zv_not_dvd_cast {m : ℕ} (hm : ¬ ℓ ∣ m) : ¬ (ℓ : ℤ_[ℓ]) ∣ (m : ℤ_[ℓ]) := by sorry

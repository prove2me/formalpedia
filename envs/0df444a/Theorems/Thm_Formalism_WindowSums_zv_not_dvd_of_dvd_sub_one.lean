-- Prove2me | Theorems.Thm_Formalism_WindowSums_zv_not_dvd_of_dvd_sub_one
-- name    : Formalism.WindowSums.zv_not_dvd_of_dvd_sub_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:29:05.685014+00:00
-- url     : https://prove2.me/theorems/da7aed35-7041-4112-8fe7-16472be0e35d
-- title:
--   Window Sums: zv not dvd of dvd sub one
-- statement:
--   The Window Sums construction uses the zv not dvd of dvd sub one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WindowSums/AnnihilatorPolynomials/ZpowVal.lean#L23-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WindowSums/AnnihilatorPolynomials/ZpowVal.lean#L23-L28

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

theorem Formalism.WindowSums.zv_not_dvd_of_dvd_sub_one {x : ℤ_[ℓ]} (hx : (ℓ : ℤ_[ℓ]) ∣ x - 1) : ¬ (ℓ : ℤ_[ℓ]) ∣ x := by sorry

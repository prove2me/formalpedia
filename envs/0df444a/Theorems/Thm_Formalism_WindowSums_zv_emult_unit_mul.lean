-- Prove2me | Theorems.Thm_Formalism_WindowSums_zv_emult_unit_mul
-- name    : Formalism.WindowSums.zv_emult_unit_mul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:39:33.090853+00:00
-- url     : https://prove2.me/theorems/bbda4f1e-3aae-48bc-ac0b-c71e4ddd399c
-- title:
--   Window Sums: zv emult unit mul
-- statement:
--   The Window Sums construction uses the zv emult unit mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WindowSums/AnnihilatorPolynomials/ZpowVal.lean#L19-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WindowSums/AnnihilatorPolynomials/ZpowVal.lean#L19-L21

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

theorem Formalism.WindowSums.zv_emult_unit_mul {c : ℤ_[ℓ]} (hc : IsUnit c) (y : ℤ_[ℓ]) :
    emultiplicity (ℓ : ℤ_[ℓ]) (c * y) = emultiplicity (ℓ : ℤ_[ℓ]) y := by sorry

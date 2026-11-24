-- Prove2me | Theorems.Thm_Formalism_GM_M_FB_vanish
-- name    : Formalism.GM.M.FB.vanish
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:44:44.831081+00:00
-- url     : https://prove2.me/theorems/39fe0d7f-52e7-49b9-a558-5dfbbd68002d
-- title:
--   FB: vanish
-- statement:
--   The FB construction uses the vanish property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeBij.lean#L306-L365
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeBij.lean#L306-L365

import Definitions.Def_Formalism_MahlerMeasure_IsFrozenInv
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeBij
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSimpArgs false
open Formalism Formalism.GM Formalism.GM.M Formalism.GM.M.FB
open MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

theorem Formalism.GM.M.FB.vanish (LL : Letters N) (n : ℕ) (ρ : Fin r) (G : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p])
    (hinv : IsFrozenInv p LL ρ n G) (h0 : ∀ m, kk ρ m = 0 → coeff m G = 0) : G = 0 := by sorry

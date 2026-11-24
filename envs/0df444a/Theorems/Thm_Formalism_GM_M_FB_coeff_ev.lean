-- Prove2me | Theorems.Thm_Formalism_GM_M_FB_coeff_ev
-- name    : Formalism.GM.M.FB.coeff_ev
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:44:26.219046+00:00
-- url     : https://prove2.me/theorems/13fda58c-6930-401c-827c-49a4190c0009
-- title:
--   FB: coeff ev
-- statement:
--   The FB construction uses the coeff ev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeBij.lean#L86-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeBij.lean#L86-L117

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
open Formalism Formalism.GM Formalism.GM.M Formalism.GM.M.FB
open MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

theorem Formalism.GM.M.FB.coeff_ev (ρ : Fin r) (n : ℕ) (F : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p])
    (hF : ∀ m ∈ F.support, ∑ c, m (Fin.last N, c) = n) (m' : Fin N × Fin r →₀ ℕ) :
    coeff m' (ev p ρ F) = coeff (ext n ρ m') F := by sorry

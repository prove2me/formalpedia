-- Prove2me | Theorems.Thm_Formalism_GM_M_FB_coeff_X_pderiv_castSucc
-- name    : Formalism.GM.M.FB.coeff_X_pderiv_castSucc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:16:00.202534+00:00
-- url     : https://prove2.me/theorems/7fbdb163-12e8-4b6c-b5c3-80887b680891
-- title:
--   FB: coeff X pderiv cast Succ
-- statement:
--   The FB construction uses the coeff X pderiv cast Succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeBij.lean#L292-L304
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeBij.lean#L292-L304

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

theorem Formalism.GM.M.FB.coeff_X_pderiv_castSucc (ρ : Fin r) (G : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p])
    (m : Fin (N + 1) × Fin r →₀ ℕ)
    (hG : ∀ ν : Fin (N + 1) × Fin r →₀ ℕ, kk ρ ν = kk ρ m → coeff ν G = 0)
    (i : Fin N) (a b : Fin r) :
    coeff m (X (Fin.castSucc i, a) * pderiv (Fin.castSucc i, b) G) = 0 := by sorry

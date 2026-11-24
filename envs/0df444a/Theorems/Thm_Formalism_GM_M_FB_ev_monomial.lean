-- Prove2me | Theorems.Thm_Formalism_GM_M_FB_ev_monomial
-- name    : Formalism.GM.M.FB.ev_monomial
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:16:00.067821+00:00
-- url     : https://prove2.me/theorems/5c16c585-56f9-4a0b-b588-622201689c37
-- title:
--   FB: ev monomial
-- statement:
--   The FB construction uses the ev monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeBij.lean#L65-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeBij.lean#L65-L84

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

theorem Formalism.GM.M.FB.ev_monomial (ρ : Fin r) (m : Fin (N + 1) × Fin r →₀ ℕ) (a : ℚ_[p]) :
    ev p ρ (monomial m a) =
      if (∀ c, c ≠ ρ → m (Fin.last N, c) = 0) then monomial (res m) a else 0 := by sorry

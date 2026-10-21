-- Prove2me | Theorems.Thm_BundledPay_Base_physician_gain
-- name    : BundledPay.Base.physician_gain
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:54:30.395917+00:00
-- url     : https://prove2.me/theorems/e179df57-e700-4f72-ac5f-6aec0503e026
-- title:
--   Proof of Theorem 1, p. 36 — physicians strictly benefit
-- statement:
--   Under the corrected conditions for beneficial bundling, physicians receive a strictly greater payoff at every bundled subgame-perfect equilibrium than at any fee-for-service Nash equilibrium:
--
--   $$F_p^{BP}(i_h^\sharp,i_p^\sharp,T)-F_p^{FFS}(i_h^*,i_p^*)>0.$$
--
--   This is one of the three strict comparisons required by Theorem 1.
--
--   **Formalization Note** The preprint's intermediate closed form (44) contains typographical inconsistencies. This milestone asserts its explicit concluding claim of strict physician gain, without reproducing that formula.
-- source:
--   Vlachy, Ayer, Ayvaci & Raghunathan, The Business of Healthcare: The Role of Physician Integration in Bundled Payments, SSRN preprint 3539596, p. 36, proof of Theorem 1, physician condition, eqs. (43)–(44) and closing sentence

import Mathlib
import Definitions.Def_BundledPay_Base_Model

namespace BundledPay.Base

/-- Strict physician gain in the proof of Theorem 1, p. 36.
The printed closed form (44) is dimensionally inconsistent and is not asserted here. -/
theorem physician_gain (P : Params) (hS : P.Standing) (hwq : P.wq = 0)
    (h5 : 2 * P.wb * (1 - P.I0) < P.dc + 2 * P.drp)
    (h6 : P.psi ≤ psiPlus P)
    (h7 : P.psi < psi0 P)
    (hint : P.dc < 2 * P.wb * (1 + P.I0))
    (ihF ipF : ℝ) (hF : IsNashFFS P ihF ipF)
    (rBP : ℝ) (σ : ℝ → ℝ × ℝ) (T : ℝ) (hBP : IsSPNE P rBP σ T) :
    physFFS P ihF ipF < physBP P T (σ T).1 (σ T).2 := by sorry

end BundledPay.Base

-- Prove2me | Theorems.Thm_BundledPay_Base_lemma_5_case_b
-- name    : BundledPay.Base.lemma_5_case_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:54:35.315341+00:00
-- url     : https://prove2.me/theorems/7e47c997-17c6-4169-af23-28738e2fbd73
-- title:
--   Lemma 5 Case B, p. 34 — zero gainsharing
-- statement:
--   In the base model ($w_q=0$), fix any bundled payment $r^{BP}$ and zero gainsharing $T=0$. A pair of efforts $(i_h,i_p)\in[0,1]^2$ is a pure Nash equilibrium of the bundled-payment effort game if and only if
--
--   $$i_h^\sharp=1,\qquad i_p^\sharp=\begin{cases}\dfrac{1}{1-\Psi}\Big(I_0+\dfrac{\Delta r_p}{2w_b}\Big),&\Psi\le\bar\Psi,\\[4pt] 1,&\Psi>\bar\Psi,\end{cases}$$
--
--   where $\bar\Psi=1-I_0-\Delta r_p/(2w_b)$ is threshold (4). These are the fee-for-service equilibrium efforts of Lemma 4, so with $T=0$ the bundled continuation reproduces the status quo and cannot by itself deliver a strict physician gain.
--
--   **Formalization Note** At $\Psi=\bar\Psi$ both printed cases (37) and (38) give $i_p^\sharp=1$, so the `if` with $\Psi\le\bar\Psi$ covers both. The payment $r^{BP}$ is additive in the hospital's payoff and does not affect the equilibrium.
-- source:
--   Vlachy, Ayer, Ayvaci & Raghunathan, The Business of Healthcare: The Role of Physician Integration in Bundled Payments, SSRN preprint 3539596, p. 34, Lemma 5 Case B, eqs. (37)–(38)

import Mathlib
import Definitions.Def_BundledPay_Base_Model

namespace BundledPay.Base

/-- Lemma 5 Case B, p. 34, (37)–(38): with zero gainsharing the BP effort equilibria
are exactly `i♯_h = 1` and `i♯_p = (I0 + Δr_p/(2w_b))/(1 − Ψ)` if `Ψ ≤ Ψ̄`, else `i♯_p = 1`. -/
theorem lemma_5_case_b (P : Params) (hS : P.Standing) (hwq : P.wq = 0)
    (rBP ih ip : ℝ) :
    IsNashBP P rBP 0 ih ip ↔
      (ih = 1 ∧ ip = (if P.psi ≤ psiBar P then
        (P.I0 + P.drp / (2 * P.wb)) / (1 - P.psi) else 1)) := by sorry

end BundledPay.Base

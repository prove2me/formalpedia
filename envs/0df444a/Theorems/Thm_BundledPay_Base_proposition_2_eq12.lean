-- Prove2me | Theorems.Thm_BundledPay_Base_proposition_2_eq12
-- name    : BundledPay.Base.proposition_2_eq12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:54:28.688808+00:00
-- url     : https://prove2.me/theorems/186d0428-ef6c-4f17-a9bb-3fff9623cd06
-- title:
--   Proposition 2, p. 19 — payer savings formula (12)
-- statement:
--   Let $\Sigma$ be the difference between total fee-for-service payer payment and the hospital's break-even bundled payment at equilibrium. Under the corrected conditions for beneficial bundling, every fee-for-service equilibrium and bundled subgame-perfect equilibrium give
--
--   $$\Sigma=\begin{cases}\dfrac{(\Delta c+2\Delta r_p-2w_b(1-I_0))^2}{8w_b},&\Psi\le\bar\Psi,\\ \dfrac{(\Delta c+2w_b(1-I_0))^2}{8w_b}-(\Delta c+\Delta r_p)\Psi,&\Psi>\bar\Psi.\end{cases}$$
--
--   This quantity is the payer margin available when choosing a bundled payment above the hospital's break-even level.
--
--   **Formalization Note** Only equation (12) is asserted here. The hypotheses are those of Theorem 1 with (7) as printed ($\Psi\le\Psi_0$), plus the interior condition $\Delta c<2w_b(1+I_0)$ of Lemma 5 (34), which selects the equilibrium regime $0<T<T_{\max}$ that the paper's proof of (12) uses (p. 37). At $\Psi=\Psi_0>\bar\Psi$ both $T=0$ and the interior $T$ are optimal for the hospital and both give $\Sigma=0$, which is the value of (12) there.
-- source:
--   Vlachy, Ayer, Ayvaci & Raghunathan, The Business of Healthcare: The Role of Physician Integration in Bundled Payments, SSRN preprint 3539596, p. 19, Proposition 2, eq. (12)

import Mathlib
import Definitions.Def_BundledPay_Base_Model

namespace BundledPay.Base

/-- Proposition 2, equation (12), p. 19: savings at a BP equilibrium, under the
conditions of Theorem 1 with (7) read as printed (`Ψ ≤ Ψ_0`). -/
theorem proposition_2_eq12 (P : Params) (hS : P.Standing) (hwq : P.wq = 0)
    (h5 : 2 * P.wb * (1 - P.I0) < P.dc + 2 * P.drp)
    (h6 : P.psi ≤ psiPlus P)
    (h7 : P.psi ≤ psi0 P)
    (hint : P.dc < 2 * P.wb * (1 + P.I0))
    (ihF ipF : ℝ) (hF : IsNashFFS P ihF ipF)
    (rBP : ℝ) (σ : ℝ → ℝ × ℝ) (T : ℝ) (hBP : IsSPNE P rBP σ T) :
    savings P ihF ipF T (σ T).1 (σ T).2 =
      if P.psi ≤ psiBar P then
        (P.dc + 2 * P.drp - 2 * P.wb * (1 - P.I0)) ^ 2 / (8 * P.wb)
      else
        (P.dc + 2 * P.wb * (1 - P.I0)) ^ 2 / (8 * P.wb) -
          (P.dc + P.drp) * P.psi := by sorry

end BundledPay.Base

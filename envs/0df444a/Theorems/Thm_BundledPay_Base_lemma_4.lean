-- Prove2me | Theorems.Thm_BundledPay_Base_lemma_4
-- name    : BundledPay.Base.lemma_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T05:54:32.891084+00:00
-- url     : https://prove2.me/theorems/9470ef39-409d-44e3-9cfc-62495298067a
-- title:
--   Lemma 4, p. 33 — FFS equilibrium efforts
-- statement:
--   In the base model, the unique pure Nash equilibrium of the fee-for-service effort game has hospital effort $i_h^*=1$ and physician effort
--
--   $$i_p^*=\begin{cases}\dfrac{I_0+\Delta r_p/(2w_b)}{1-\Psi},&\Psi\le\bar\Psi,\\1,&\Psi>\bar\Psi,\end{cases}$$
--
--   where $\bar\Psi=1-I_0-\Delta r_p/(2w_b)$. This characterizes the status-quo actions used in the payment comparisons.
--
--   **Formalization Note** The overlap at $\Psi=\bar\Psi$ has the same value in both branches; the first branch is selected there.
-- source:
--   Vlachy, Ayer, Ayvaci & Raghunathan, The Business of Healthcare: The Role of Physician Integration in Bundled Payments, SSRN preprint 3539596, p. 33, Lemma 4, eqs. (26)–(27)

import Mathlib
import Definitions.Def_BundledPay_Base_Model

namespace BundledPay.Base

/-- Lemma 4, p. 33: the unique FFS equilibrium effort profile. -/
theorem lemma_4 (P : Params) (hS : P.Standing) (hwq : P.wq = 0)
    (ih ip : ℝ) :
    IsNashFFS P ih ip ↔
      (ih = 1 ∧ ip = (if P.psi ≤ psiBar P then
        (P.I0 + P.drp / (2 * P.wb)) / (1 - P.psi) else 1)) := by sorry

end BundledPay.Base

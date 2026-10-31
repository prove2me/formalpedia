-- Prove2me | Theorems.Thm_BundledPay_Base_lemma_1
-- name    : BundledPay.Base.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T05:54:22.733394+00:00
-- url     : https://prove2.me/theorems/c6277a0e-0e7d-4ee9-9761-939106a7357c
-- title:
--   Lemma 1, p. 14 — status-quo intensity
-- statement:
--   In the base model, at every pure Nash equilibrium of fee-for-service effort choices the care intensity is
--
--   $$I^*=\begin{cases}I_0+\dfrac{\Delta r_p}{2w_b},&\Psi\le\bar\Psi,\\1-\Psi,&\Psi>\bar\Psi,\end{cases}\qquad \bar\Psi=1-I_0-\frac{\Delta r_p}{2w_b}.$$
--
--   The threshold separates the range where the physicians determine intensity from the range where the effort boundary constrains it.
-- source:
--   Vlachy, Ayer, Ayvaci & Raghunathan, The Business of Healthcare: The Role of Physician Integration in Bundled Payments, SSRN preprint 3539596, p. 14, Lemma 1 and eq. (4)

import Mathlib
import Definitions.Def_BundledPay_Base_Model

namespace BundledPay.Base

/-- Lemma 1, p. 14: status-quo equilibrium intensity. -/
theorem lemma_1 (P : Params) (hS : P.Standing) (hwq : P.wq = 0)
    (ih ip : ℝ) (hF : IsNashFFS P ih ip) :
    intensity P ih ip =
      if P.psi ≤ psiBar P then P.I0 + P.drp / (2 * P.wb)
      else 1 - P.psi := by sorry

end BundledPay.Base

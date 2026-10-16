-- Prove2me | Theorems.Thm_CustomerVoice_OLearn_seller_acceptance
-- name    : CustomerVoice.OLearn.seller_acceptance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T01:07:47.094291+00:00
-- url     : https://prove2.me/theorems/d865220c-3eb2-4ff9-b281-0c727decc2c1
-- title:
--   §3.3, p. 16 — the seller accepts a request q from a buyer believed to be θ̂ iff q ≤ γθ̂/(s+γk)
-- statement:
--   Under the standing assumptions, let $\hat\theta\in\{\theta_H,\theta_L\}$ be the seller's belief about a buyer, and let $q\ge 0$ be the buyer's quality request. The seller accepts the request (that is, $\gamma(\hat\theta q-kq^2)-sq^2\ge 0$) if and only if
--   $$q \le \frac{\gamma\hat\theta}{s+\gamma k}.$$
--
--   This turns the acceptance inequality into the upper bound on acceptable requests that the rest of the O-Learning analysis uses.
--
--   **Formalization Note** The restriction $q \ge 0$ is needed: for $q<0$ the acceptance inequality fails while the bound holds. Requests are in $\mathbb R_+$ in the paper (p. 9).
-- source:
--   Guo, The Voice of Customers in Customization, SSRN working paper 3994319 (version of 2023-11-29, https://ssrn.com/abstract=3994319), p. 16, §3.3, before (9)

import Mathlib
import Definitions.Def_CustomerVoice_OLearn_Setting

namespace CustomerVoice.OLearn

theorem seller_acceptance (M : Model) (hM : M.Standing) :
    ∀ t : CustomerVoice.ALearn.BType, ∀ q : ℝ, 0 ≤ q →
      (M.accepts (M.θ t) q ↔ q ≤ M.γ * M.θ t / (M.s + M.γ * M.k)) := by sorry

end CustomerVoice.OLearn

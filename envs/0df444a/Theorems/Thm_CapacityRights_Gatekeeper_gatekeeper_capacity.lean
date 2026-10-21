-- Prove2me | Theorems.Thm_CapacityRights_Gatekeeper_gatekeeper_capacity
-- name    : CapacityRights.Gatekeeper.gatekeeper_capacity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:38:59.098685+00:00
-- url     : https://prove2.me/theorems/341e92c9-f295-437b-8362-a6ccc0fe29ec
-- title:
--   Proof of Proposition 3: negotiated rights induce efficient total capacity
-- statement:
--   Assume both divisions satisfy the paper's positive dedicated-capacity condition (20), the capacity charge follows the annuity rule, and $k^*$ maximizes the firm's net present value. Then there is a negotiated downstream capacity right $k_2^*$ with $0\le k_2^*<k^*$ such that Division 1's best response is to install $k^*-k_2^*$ units for itself. Hence the total installed capacity is efficient:
--
--   $$
--   k_2^*+\bigl(k^*-k_2^*\bigr)=k^*.
--   $$
--
--   The same right works for every period and every fixed payment, because the payment does not depend on Division 1's capacity choice. This is the capacity-choice part of the gatekeeper result.
--
--   **Formalization Note** $k^*$ is a global maximizer, and the right is existentially determined. The statement does not prescribe it by a separate formula.
-- source:
--   Dutta & Reichelstein, Capacity Rights and Full Cost Transfer Pricing, CESifo Working Paper No. 7968 (November 2019), p. 44 (PDF 47), proof of Proposition 3, Intermediate Value Theorem claim

import Mathlib
import Definitions.Def_CapacityRights_Gatekeeper_Model

namespace CapacityRights.Gatekeeper

open MeasureTheory

/-- Existence claim in the proof of Proposition 3, p. 44 (PDF 47). -/
theorem gatekeeper_capacity (E : Env) (hS : E.Standing)
    (h20_1 : ucc E + E.w1 < ∫ e, deriv (fun q => E.R1 q e.1) 0 ∂E.μ)
    (h20_2 : ucc E + E.w2 < ∫ e, deriv (fun q => E.R2 q e.2) 0 ∂E.μ)
    (d : ℕ → ℝ) (hd : IsAnnuity E d)
    (kstar : ℝ) (hk : IsEfficient E kstar) :
    ∃ k2 ∈ Set.Ico 0 kstar,
      ∀ t ∈ Finset.Icc 1 E.T, ∀ p : ℝ,
        IsBestResponse1 E d t k2 p (kstar - k2) := by sorry

end CapacityRights.Gatekeeper

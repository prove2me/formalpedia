-- Prove2me | Theorems.Thm_CapacityRights_Gatekeeper_proposition_3
-- name    : CapacityRights.Gatekeeper.proposition_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T12:39:13.516161+00:00
-- url     : https://prove2.me/theorems/da9ac612-533f-4350-a77f-4808adfbc782
-- title:
--   Proposition 3: a negotiated gatekeeper contract achieves strong goal congruence
-- statement:
--   Consider a stationary two-division firm with fungible capacity, period-by-period renegotiation of initial capacity rights, and annuity depreciation. Let $k^*$ maximize the firm's net present value, and suppose each division's expected marginal revenue at zero exceeds its variable cost plus the user cost $c$ of capacity, as in condition (20). There exist a negotiated downstream capacity right $k_2^*$ and a fixed period payment $p$ such that
--
--   $$
--   0\le k_2^*<k^*,\qquad TP_t(k_2^*,q_{2t})=p+w_2q_{2t}.
--   $$
--
--   For every period, Division 1's best response is to install $k^*-k_2^*$ units for itself, so total installed capacity is $k^*$. A best response also exists under the no-contract default $(k_2,p)=(0,0)$. Relative to every such default best response, the negotiated contract gives both divisions at least as much expected period payoff. Production after renegotiation maximizes the total contribution margin.
--
--   This expresses the paper's strong goal congruence result: the same efficient capacity choice is optimal in each period's expected performance measure, and the contract is acceptable to both divisions.
--
--   **Formalization Note** The preference is weak, as a zero incremental surplus need not make either division strictly better off. Both instances of condition (20) are assumed, as on p. 25. The common shock law can correlate the two divisions. The standing assumptions strengthen concavity to strict concavity and add regularity; capacity remains an argmax rather than a first-order-condition definition.
-- source:
--   Dutta & Reichelstein, Capacity Rights and Full Cost Transfer Pricing, CESifo Working Paper No. 7968 (November 2019), p. 26 (PDF 29), Proposition 3; p. 25 (PDF 28), condition (20); pp. 43–45 (PDF 46–48), proof

import Mathlib
import Definitions.Def_CapacityRights_Gatekeeper_Model

namespace CapacityRights.Gatekeeper

open MeasureTheory

/-- Proposition 3, p. 26 (PDF 29): the negotiated gatekeeper contract. -/
theorem proposition_3 (E : Env) (hS : E.Standing)
    (h20_1 : ucc E + E.w1 < ∫ e, deriv (fun q => E.R1 q e.1) 0 ∂E.μ)
    (h20_2 : ucc E + E.w2 < ∫ e, deriv (fun q => E.R2 q e.2) 0 ∂E.μ)
    (d : ℕ → ℝ) (hd : IsAnnuity E d)
    (kstar : ℝ) (hk : IsEfficient E kstar) :
    ∃ k2 ∈ Set.Ico 0 kstar, ∃ p : ℝ,
      (∀ t ∈ Finset.Icc 1 E.T,
        IsBestResponse1 E d t k2 p (kstar - k2)) ∧
      (∀ t ∈ Finset.Icc 1 E.T,
        ∃ khat : ℝ, IsBestResponse1 E d t 0 0 khat) ∧
      (∀ t ∈ Finset.Icc 1 E.T, ∀ khat : ℝ,
        IsBestResponse1 E d t 0 0 khat →
          RI1 E d t khat 0 0 ≤ RI1 E d t (kstar - k2) k2 p ∧
          Profit2 E khat 0 0 ≤ Profit2 E (kstar - k2) k2 p) := by sorry

end CapacityRights.Gatekeeper

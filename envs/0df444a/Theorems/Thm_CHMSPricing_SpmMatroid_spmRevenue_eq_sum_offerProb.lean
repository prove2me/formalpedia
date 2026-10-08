-- Prove2me | Theorems.Thm_CHMSPricing_SpmMatroid_spmRevenue_eq_sum_offerProb
-- name    : CHMSPricing.SpmMatroid.spmRevenue_eq_sum_offerProb
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T11:41:03.583207+00:00
-- url     : https://prove2.me/theorems/5fbf6827-5270-415c-a136-60d6fef7aa63
-- title:
--   §2.2, p. 4 — the expected revenue of an SPM is Σ_i c_i q_i p_i
-- statement:
--   Let $\mathcal S$ be a sequential posted-price mechanism with ordering $\sigma$ and prices $\mathbf p$, under any downward-closed constraint, with independent values $v_i \sim F_i$. Let $c_i$ be the probability that agent $i$ is offered service at its turn, and $q_i = 1 - F_i(p_i)$. Then
--
--   $$\mathcal R^\sigma_{\mathbf p} = \sum_i c_i\, q_i\, p_i.$$
--
--   The formula separates the event that agent $i$ is offered, which depends only on the agents approached before $i$, from $i$'s own acceptance.
--
--   **Formalization Note** $c_i$ and $q_i$ are indexed by agent, with the price $p_i$ attached to agent $i$; the page defines $c_i$ via the values of $\sigma(1), \dots, \sigma(i-1)$, which is read as "the agents approached before $i$". The prices are arbitrary reals; acceptance is $p_i \le v_i$, which has probability $1 - F_i(p_i)$ because $F_i$ has no atoms.
-- source:
--   Chawla, Hartline, Malec and Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, p. 4, §2.2, last sentence of the SPM paragraph

import Mathlib
import Definitions.Def_CHMSPricing_SpmMatroid_Spm

namespace CHMSPricing.SpmMatroid

/-- §2.2 (p. 4): the expected revenue of an SPM is `ℛ^σ_p = ∑ᵢ cᵢ qᵢ pᵢ`, where
`cᵢ` is the probability that agent `i` is offered service at its turn and `qᵢ = 1 − Fᵢ(pᵢ)`. -/
theorem spmRevenue_eq_sum_offerProb {n : ℕ} (D : Fin n → ValueDist) (J : SetSystem (Fin n))
    (σ : Equiv.Perm (Fin n)) (p : Fin n → ℝ) :
    spmRevenue D J σ p =
      ∑ i, (prior D {v | spmOffered J σ p v i}).toReal * (1 - (D i).cdf (p i)) * p i := by sorry

end CHMSPricing.SpmMatroid

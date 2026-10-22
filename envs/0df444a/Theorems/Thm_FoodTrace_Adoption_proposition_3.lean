-- Prove2me | Theorems.Thm_FoodTrace_Adoption_proposition_3
-- name    : FoodTrace.Adoption.proposition_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-22T03:45:10.39144+00:00
-- url     : https://prove2.me/theorems/32f9c13c-d472-470d-a5c6-b56135ea0556
-- title:
--   Proposition 3 — under BPC, traceability lowers the retailer's SPNE profit exactly for r ∈ (r₁, r₂), r^e_N < r₁ < r^e_T < r₂
-- statement:
--   Under the standing assumptions ($n \ge 2$, $0 \le \rho_e < \rho < 1$, $e > 0$, $0 < c_p < \bar c_p$), suppose the Break Point Criterion $\pi^e_{0T}(r^e_T) < \pi^e_{0N}(r^e_T)$ holds. Then there exist intersection points $r_1, r_2$ with
--   $$r^e_N < r_1 < r^e_T < r_2, \qquad \pi^o_{0T}(r_1) = \pi^e_{0N}(r_1), \qquad \pi^e_{0T}(r_2) = \pi^e_{0N}(r_2),$$
--   where $\pi^o_{0T}(r) = n(1-\rho)r - nc_p$, $\pi^e_{0T}(r) = n(1-\rho_e)(r - w^e_T)$ and $\pi^e_{0N}(r) = n(1-\rho_e)^n(r - w^e_N)$, such that:
--
--   1. both games, without and with traceability, have a subgame-perfect equilibrium at every retail price $r$;
--   2. for $r \in (r_1, r_2)$, the retailer's SPNE profit with traceability is strictly lower than without;
--   3. for every other $r$, her SPNE profit with traceability is at least as high as without.
--
--   This is the paper's headline: traceability, though it removes the cascade threat, can lower the equilibrium profit of the chain's most powerful member, exactly on an interval of retail prices around the effort threshold $r^e_T$.
--
--   **Formalization Note** The retailer's profit is her profit at a subgame-perfect equilibrium of the three-stage game (with the tie and selection rules of p. 8), not the closed forms of Tables EC.1–EC.2; the comparison is made for every pair of equilibria, and the existence of equilibria is part of the conclusion. "Otherwise, traceability adoption increases the retailer's profit" is rendered as "at least as high" (≥): the two profits are equal at $r_1$, at $r_2$ and for $r \le r^o_T$ (finding F1). The intersection equations are between the closed-form branch profits, as printed.
-- source:
--   Dong, Jiang & Xu, Impact of Traceability Technology Adoption in Food Supply Chain Networks, Management Science (accepted manuscript, SSRN 3484664, March 2022), p. 21, Proposition 3

import Mathlib
import Definitions.Def_FoodTrace_Adoption_Model

namespace FoodTrace.Adoption

/-- Proposition 3 (p. 21): if BPC holds, there are `r₁ ∈ (r^e_N, r^e_T)` and `r₂ ∈ (r^e_T, ∞)` with
`π^o_0T(r₁) = π^e_0N(r₁)` and `π^e_0T(r₂) = π^e_0N(r₂)`, both games have an SPNE at every retail
price, and the retailer's SPNE profit is strictly lower with traceability for `r ∈ (r₁, r₂)` and
at least as high otherwise ("increases" read as `≥`). -/
theorem proposition_3 (P : Params) (hP : Standing P) (hBPC : BPC P) :
    ∃ r₁ r₂ : ℝ, rNe P < r₁ ∧ r₁ < rTe P ∧ rTe P < r₂ ∧
      pi0To P r₁ = pi0Ne P r₁ ∧ pi0Te P r₂ = pi0Ne P r₂ ∧
      (∀ r : ℝ, (∃ s : Strategy P, IsSPNE .N P r s) ∧ (∃ s : Strategy P, IsSPNE .T P r s)) ∧
      ∀ (r : ℝ) (sN sT : Strategy P), IsSPNE .N P r sN → IsSPNE .T P r sT →
        (r₁ < r → r < r₂ → retailerProfit .T P r sT < retailerProfit .N P r sN) ∧
        (¬ (r₁ < r ∧ r < r₂) → retailerProfit .N P r sN ≤ retailerProfit .T P r sT) := by sorry

end FoodTrace.Adoption

-- Prove2me | Theorems.Thm_FoodTrace_Adoption_proposition_1
-- name    : FoodTrace.Adoption.proposition_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-22T03:45:12.624983+00:00
-- url     : https://prove2.me/theorems/2d52a548-8869-419e-8232-fcca3ec25226
-- title:
--   Proposition 1 — the SPNE without traceability: (w^e_N, p^e_N, eI) for r ≥ r^e_N, (w^o_N, p^o_N, 0) for r^o_N ≤ r < r^e_N
-- statement:
--   Consider Case N under the standing assumptions, with $r^o_N = w^o_N = p^o_N$ and
--   $$r^e_N = \max\Big\{\frac{(1-\rho_e)^{n+1}e - [2(1-\rho_e)^n - (1-\rho)^n]\rho_\tau c_p}{\rho_\tau\,\ell^2},\; p^e_N\Big\}.$$
--   A subgame-perfect equilibrium exists at every retail price $r$. Moreover, at every SPNE:
--
--   1. If $c_p < \underline c_p$, then $p^o_N < p^e_N < w^e_N < r^e_N$; for $r \ge r^e_N$ the retailer offers $w^e_N$, tier-1 answers $p^e_N$ and all farms exert effort; for $r^o_N \le r < r^e_N$ the retailer offers $w^o_N$, tier-1 answers $p^o_N$ and no farm exerts effort.
--   2. If $\underline c_p \le c_p$, then $p^o_N \ge p^e_N = w^e_N = r^e_N$, and for $r \ge r^e_N$ the outcome is $(w^e_N, p^e_N)$ with all farms exerting effort.
--   3. The supply chain trades if and only if $r \ge \min\{r^e_N, r^o_N\}$.
--
--   This determines the retailer's equilibrium profit without traceability.
--
--   **Formalization Note** An SPNE is a tier-2 selected outcome at every $p$, a tier-1 best response at every $w$ and an optimal retailer choice at $r$, each with the tie rules of p. 8; choices range over all real prices and "no trade".
-- source:
--   Dong, Jiang & Xu, Impact of Traceability Technology Adoption in Food Supply Chain Networks, Management Science (accepted manuscript, SSRN 3484664, March 2022), p. 11, Proposition 1

import Mathlib
import Definitions.Def_FoodTrace_Adoption_Model

namespace FoodTrace.Adoption

/-- Proposition 1 (p. 11): the SPNE without traceability. An SPNE exists at every retail price;
for `r ≥ r^e_N` it is `(w^e_N, p^e_N, eI)` and, when `0 < c_p < c̲_p`, `(w^o_N, p^o_N, 0)` for
`r^o_N ≤ r < r^e_N`; the chain trades iff `r ≥ min{r^e_N, r^o_N}`. -/
theorem proposition_1 (P : Params) (hP : Standing P) :
    (∀ r : ℝ, ∃ s : Strategy P, IsSPNE .N P r s) ∧
    (P.cp < cpLow P → pNo P < pNe P ∧ pNe P < wNe P ∧ wNe P < rNe P ∧
      ∀ (r : ℝ) (s : Strategy P), IsSPNE .N P r s →
        (rNe P ≤ r → s.w = some (wNe P) ∧ s.σ₁ (wNe P) = some (pNe P) ∧
          s.σ₂ (pNe P) = some (allEffort P)) ∧
        (rNo P ≤ r → r < rNe P → s.w = some (wNo P) ∧ s.σ₁ (wNo P) = some (pNo P) ∧
          s.σ₂ (pNo P) = some (noEffort P))) ∧
    (cpLow P ≤ P.cp → pNe P ≤ pNo P ∧ pNe P = wNe P ∧ wNe P = rNe P ∧
      ∀ (r : ℝ) (s : Strategy P), IsSPNE .N P r s →
        rNe P ≤ r → s.w = some (wNe P) ∧ s.σ₁ (wNe P) = some (pNe P) ∧
          s.σ₂ (pNe P) = some (allEffort P)) ∧
    (∀ (r : ℝ) (s : Strategy P), IsSPNE .N P r s → (Trades s ↔ min (rNe P) (rNo P) ≤ r)) := by sorry

end FoodTrace.Adoption

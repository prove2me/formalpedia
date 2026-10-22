-- Prove2me | Theorems.Thm_FoodTrace_Adoption_proposition_2
-- name    : FoodTrace.Adoption.proposition_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-22T03:45:09.041525+00:00
-- url     : https://prove2.me/theorems/9330feb4-63b1-4da5-97c9-c3d3e534e1a0
-- title:
--   Proposition 2 — the SPNE with traceability: (w^e_T, p^e_T, eI) for r ≥ r^e_T, (w^o_T, p^o_T, 0) for r^o_T ≤ r < r^e_T
-- statement:
--   Consider Case T under the standing assumptions, with $r^o_T = w^o_T = p^o_T = \frac{c_p}{1-\rho}$ and
--   $$r^e_T = \frac{(1-\rho_e)^2 e - (1+\rho-2\rho_e)\rho_\tau c_p}{\rho_\tau^3}.$$
--   Then $r^o_T = w^o_T = p^o_T < p^e_T < w^e_T < r^e_T$, a subgame-perfect equilibrium exists at every retail price $r$, and at every SPNE:
--
--   1. for $r \ge r^e_T$ the retailer offers $w^e_T$, tier-1 answers $p^e_T$ and all farms exert effort;
--   2. for $r^o_T \le r < r^e_T$ the retailer offers $w^o_T$, tier-1 answers $p^o_T$ and no farm exerts effort;
--   3. the supply chain trades if and only if $r \ge r^o_T$.
--
--   This determines the retailer's equilibrium profit with traceability.
--
--   **Formalization Note** The SPNE is the same notion as in Proposition 1, for the Case T payoffs.
-- source:
--   Dong, Jiang & Xu, Impact of Traceability Technology Adoption in Food Supply Chain Networks, Management Science (accepted manuscript, SSRN 3484664, March 2022), p. 14, Proposition 2

import Mathlib
import Definitions.Def_FoodTrace_Adoption_Model

namespace FoodTrace.Adoption

/-- Proposition 2 (p. 14): the SPNE with traceability. `r^o_T = w^o_T = p^o_T < p^e_T < w^e_T <
r^e_T`; an SPNE exists at every retail price; it is `(w^e_T, p^e_T, eI)` for `r ≥ r^e_T` and
`(w^o_T, p^o_T, 0)` for `r^o_T ≤ r < r^e_T`; the chain trades iff `r ≥ r^o_T`. -/
theorem proposition_2 (P : Params) (hP : Standing P) :
    rTo P = wTo P ∧ wTo P = pTo P ∧ pTo P < pTe P ∧ pTe P < wTe P ∧ wTe P < rTe P ∧
    (∀ r : ℝ, ∃ s : Strategy P, IsSPNE .T P r s) ∧
    ∀ (r : ℝ) (s : Strategy P), IsSPNE .T P r s →
      (rTe P ≤ r → s.w = some (wTe P) ∧ s.σ₁ (wTe P) = some (pTe P) ∧
        s.σ₂ (pTe P) = some (allEffort P)) ∧
      (rTo P ≤ r → r < rTe P → s.w = some (wTo P) ∧ s.σ₁ (wTo P) = some (pTo P) ∧
        s.σ₂ (pTo P) = some (noEffort P)) ∧
      (Trades s ↔ rTo P ≤ r) := by sorry

end FoodTrace.Adoption

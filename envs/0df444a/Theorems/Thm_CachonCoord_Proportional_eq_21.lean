-- Prove2me | Theorems.Thm_CachonCoord_Proportional_eq_21
-- name    : CachonCoord.Proportional.eq_21
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:44:10.926935+00:00
-- url     : https://prove2.me/theorems/18edda1f-9318-497a-98c6-2511037a077b
-- title:
--   Eq. (21), p. 51 — at any Nash equilibrium q*_i > 0, the first order condition holds and q*_i is given by (21)
-- statement:
--   Let $n \ge 2$ and $b < w < p$. At any Nash equilibrium $q^*$ of the $n$-retailer game, with $q^* = \sum_j q^*_j$ and $q^*_{-i} = q^* - q^*_i$, every retailer $i$ orders a positive amount, satisfies the first order condition $\partial\pi_i/\partial q_i = 0$, equivalently
--
--   $$
--   q^*\left(\frac{p-w}{p-b}\right) - q_i^*F(q^*) - q_{-i}^*\left(\frac1{q^*}\int_0^{q^*}F(x)\,dx\right) = 0,
--   $$
--
--   and therefore
--
--   $$
--   q_i^* = q^*\,\frac{\dfrac{p-w}{p-b} - \dfrac1{q^*}\displaystyle\int_0^{q^*}F(x)\,dx}{F(q^*) - \dfrac1{q^*}\displaystyle\int_0^{q^*}F(x)\,dx}. \qquad (21)
--   $$
--
--   Given the total, (21) pins down each retailer's equilibrium order. Combined with $q^* = nq^*_i$ it yields (22).
--
--   **Formalization Note** The book's "any Nash equilibrium must satisfy each retailer's first order condition" presumes interior orders; the statement includes that every equilibrium order is positive, which rules out equilibria where some retailers order $0$ (and the all-zero profile). The parameter range $b < w < p$ is the section's (p. 51). The hypotheses on the demand law are the chapter's standing assumptions (p. 7), carried by the model.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.5.1, p. 51 (first order condition and Eq. (21))

import Mathlib
import Definitions.Def_CachonCoord_Proportional_Demand
import Definitions.Def_CachonCoord_Proportional_Nash
import Definitions.Def_CachonCoord_Proportional_Game

namespace CachonCoord.Proportional

/-- p. 51, the first order condition and Eq. (21): when `b < w < p`, at any Nash equilibrium
`q*` of the `n`-retailer game every retailer orders a positive amount, satisfies the first order
condition `∂π_i/∂q_i = 0`, i.e. (in the page's scaling)
`q* (p − w)/(p − b) − q*_i F(q*) − q*_{−i} (1/q*) ∫_0^{q*} F = 0`, and hence
`q*_i = q* ((p − w)/(p − b) − (1/q*) ∫_0^{q*} F) / (F(q*) − (1/q*) ∫_0^{q*} F)`, where
`q* = ∑_j q*_j` and `q*_{−i} = q* − q*_i`. -/
theorem eq_21 (M : Model) (n : ℕ) (hn : 2 ≤ n) (w b : ℝ) (hbw : b < w) (hwp : w < M.p)
    (q : Fin n → ℝ) (hq : M.IsNashEq w b q) (i : Fin n) :
    0 < q i ∧
      HasDerivAt (fun y => M.retailerProfit w b y (Model.total q - q i)) 0 (q i) ∧
      Model.total q * ((M.p - w) / (M.p - b)) - q i * M.F (Model.total q) -
          (Model.total q - q i) * M.avgF (Model.total q) = 0 ∧
      q i = Model.total q * ((M.p - w) / (M.p - b) - M.avgF (Model.total q)) /
          (M.F (Model.total q) - M.avgF (Model.total q)) := by sorry

end CachonCoord.Proportional

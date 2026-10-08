-- Prove2me | Theorems.Thm_CachonCoord_EffortNewsvendor_sec_6_4_1_effort_coordination
-- name    : CachonCoord.EffortNewsvendor.sec_6_4_1_effort_coordination
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:33:21.444258+00:00
-- url     : https://prove2.me/theorems/41488be9-15cb-4c34-9db6-476496e50a12
-- title:
--   §6.4.1, pp. 42–43 — buy-backs distort effort (19); the quantity discount w_d gives λΠ(q, e°), the chain's effort incentive and the order q°
-- statement:
--   Consider the newsvendor of §6.4.1, in which the retailer chooses an order quantity $q$ and an unverifiable effort level $e \ge 0$. The channel's profit is $\Pi(q, e) = pS(q, e) - cq - g(e)$. The following hold.
--
--   1. **Buy backs distort effort (Eq. (19)).** For a buy back contract with $b > 0$ and any wholesale price $w_b$, at every $q > 0$ and $e > 0$,
--   $$
--   \frac{\partial \pi_r(q, e, w_b, b)}{\partial e} < \frac{\partial \Pi(q, e)}{\partial e}.
--   $$
--   2. **The quantity discount aligns effort and splits profit.** Let $e^o \ge 0$, $\lambda \in [0, 1]$, and let the retailer pay $w_d(q)q$ with
--   $$
--   w_d(q) = (1 - \lambda)p\,\frac{S(q, e^o)}{q} + \lambda c - (1 - \lambda)\frac{g(e^o)}{q}.
--   $$
--   Then for every $q > 0$:
--      - the retailer earns $\pi_r(q, e^o) = \lambda \Pi(q, e^o)$ and the supplier $\pi_s(q) = (1 - \lambda)\Pi(q, e^o)$;
--      - at every effort $e > 0$, $\partial \pi_r(q, e)/\partial e = \partial \Pi(q, e)/\partial e$, so the retailer's effort first-order condition is the chain's condition (18);
--      - an effort level $e \ge 0$ maximizes $\pi_r(q, \cdot)$ over $[0, \infty)$ if and only if it maximizes $\Pi(q, \cdot)$.
--   3. **The optimal order.** If $(q^o, e^o)$, with $q^o > 0$ and $e^o \ge 0$, maximizes $\Pi$ over $q \ge 0$, $e \ge 0$, then under $w_d$ with $\lambda \in [0, 1]$ the order $q^o$ maximizes both the retailer's $q \mapsto \pi_r(q, e^o)$ and the supplier's $\pi_s$ over $q > 0$.
--
--   The buy back, quantity-flexibility and revenue-sharing contracts that coordinate the standard newsvendor distort the retailer's effort; the quantity discount keeps the effort incentive intact and allocates the channel's profit $\Pi(q^o, e^o)$ in any proportion $\lambda$.
--
--   **Formalization Note** Clause 3 is the page's "Given the optimal effort $e^o$ … the retailer's optimal order quantity is $q^o$". It is a statement at $e = e^o$. Clauses 2 and 3 together do not make $(q^o, e^o)$ a joint maximizer of the retailer's profit, and the formalization does not claim that. The sign of the $g(e^o)/q$ term of $w_d$ corrects the page's print (see the definition). The schedule divides by $q$, so $q > 0$ and $q^o > 0$ are assumed.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.4.1, Eq. (19), p. 42, and the quantity discount, p. 43

import Mathlib
import Definitions.Def_CachonCoord_EffortNewsvendor_Model
import Definitions.Def_CachonCoord_EffortNewsvendor_Contracts

namespace CachonCoord.EffortNewsvendor

/-- §6.4.1, pp. 42–43. (1) Eq. (19): with a buy back contract and `b > 0`, the retailer's
marginal profit of effort is strictly below the channel's at every `q > 0`, `e > 0`.
(2) The quantity discount `w_d` with `λ ∈ [0, 1]`, built on an effort `e° ≥ 0`: for every
`q > 0`, `π_r(q, e°) = λΠ(q, e°)` and the supplier earns `π_s(q) = (1 − λ)Π(q, e°)`; for every
`q > 0` the retailer's profit and the channel's have the same derivative in effort at every
`e > 0`, and the same maximizers over effort levels `e ≥ 0`.
(3) If `(q°, e°)`, `q° > 0`, `e° ≥ 0`, maximizes `Π` over `q ≥ 0`, `e ≥ 0`, then under `w_d` with
`λ ∈ [0, 1]` the order `q°` maximizes both `q ↦ π_r(q, e°)` and `q ↦ π_s(q)` over `q > 0`. -/
theorem sec_6_4_1_effort_coordination (M : Model) :
    (∀ wb b q e : ℝ, 0 < b → 0 < q → 0 < e →
      ∃ d₁ d₂ : ℝ, HasDerivAt (fun e' => M.bbRetailerProfit wb b q e') d₁ e ∧
        HasDerivAt (fun e' => M.Pi q e') d₂ e ∧ d₁ < d₂) ∧
    (∀ lam eo : ℝ, 0 ≤ lam → lam ≤ 1 → 0 ≤ eo →
      (∀ q : ℝ, 0 < q → M.qdRetailerProfit lam eo q eo = lam * M.Pi q eo) ∧
      (∀ q : ℝ, 0 < q → M.qdSupplierProfit lam eo q = (1 - lam) * M.Pi q eo) ∧
      (∀ q e : ℝ, 0 < q → 0 < e →
        ∃ d : ℝ, HasDerivAt (fun e' => M.qdRetailerProfit lam eo q e') d e ∧
          HasDerivAt (fun e' => M.Pi q e') d e) ∧
      (∀ q e : ℝ, 0 < q → 0 ≤ e →
        (IsMaxOn (fun e' => M.qdRetailerProfit lam eo q e') (Set.Ici 0) e ↔
          IsMaxOn (fun e' => M.Pi q e') (Set.Ici 0) e))) ∧
    (∀ lam qo eo : ℝ, 0 ≤ lam → lam ≤ 1 → 0 < qo → 0 ≤ eo →
      IsMaxOn (fun x : ℝ × ℝ => M.Pi x.1 x.2) (Set.Ici 0 ×ˢ Set.Ici 0) (qo, eo) →
      IsMaxOn (fun q => M.qdRetailerProfit lam eo q eo) (Set.Ioi 0) qo ∧
        IsMaxOn (fun q => M.qdSupplierProfit lam eo q) (Set.Ioi 0) qo) := by sorry

end CachonCoord.EffortNewsvendor

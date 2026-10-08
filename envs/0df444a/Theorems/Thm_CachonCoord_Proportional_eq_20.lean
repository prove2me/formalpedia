-- Prove2me | Theorems.Thm_CachonCoord_Proportional_eq_20
-- name    : CachonCoord.Proportional.eq_20
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:31:16.298909+00:00
-- url     : https://prove2.me/theorems/d809ad84-c19b-444a-8715-666c964f155c
-- title:
--   Eq. (20), p. 50 — the integrated chain is a newsvendor: q° maximizes Π iff F(q°) = (p − c)/p
-- statement:
--   In the competing-newsvendor model with proportional allocation, total sales depend only on the total stock $q$, so the integrated supply chain solves the single newsvendor problem of maximizing $\Pi(q) = pS(q) - cq$ over $q \ge 0$, where $S(q) = \mathbb E[\min(q,D)]$.
--
--   There exists $q^o > 0$ with
--
--   $$
--   F(q^o) = \frac{p-c}{p},
--   $$
--
--   and a quantity $q \ge 0$ maximizes $\Pi$ over $[0,\infty)$ if and only if $F(q) = (p-c)/p$.
--
--   This is the benchmark the decentralized contracts are measured against: a contract coordinates the chain when the retailers' equilibrium total order is $q^o$.
--
--   **Formalization Note** The book says "the optimal order quantity is defined by" (20); both the existence of a solution and the equivalence with optimality are stated. The hypotheses on the demand law are the chapter's standing assumptions (p. 7), carried by the model.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.5.1, Eq. (20), p. 50

import Mathlib
import Definitions.Def_CachonCoord_Proportional_Demand

namespace CachonCoord.Proportional

/-- Eq. (20), p. 50: the integrated supply chain faces a single newsvendor problem, whose
optimal order quantity `q°` is defined by `F(q°) = (p − c)/p`. Such a `q° > 0` exists, and a
quantity `q ≥ 0` maximizes the chain profit `Π(q) = pS(q) − cq` over `q ≥ 0` exactly when
`F(q) = (p − c)/p`. -/
theorem eq_20 (M : Model) :
    (∃ qo : ℝ, 0 < qo ∧ M.F qo = (M.p - M.c) / M.p) ∧
      ∀ q : ℝ, 0 ≤ q →
        (IsMaxOn M.chainProfit (Set.Ici 0) q ↔ M.F q = (M.p - M.c) / M.p) := by sorry

end CachonCoord.Proportional

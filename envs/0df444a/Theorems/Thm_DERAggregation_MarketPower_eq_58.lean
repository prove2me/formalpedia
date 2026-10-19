-- Prove2me | Theorems.Thm_DERAggregation_MarketPower_eq_58
-- name    : DERAggregation.MarketPower.eq_58
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T11:25:01.400181+00:00
-- url     : https://prove2.me/theorems/b40b61a7-d841-4fa2-ae03-23dac5332422
-- title:
--   (58), §5.1.2, p. 29 — the participation market-clearing price λ^S(y) = (y + C + Σ b_i/(2a_i)) / Σ 1/(2a_i)
-- statement:
--   Consider the single-node market of §5 with prosumer participation, under Assumption 5. Fix a total generator supply $y\ge0$. A price $\lambda$ and net purchases $z$ clear the market at $y$ — every $z_i$ maximizes $u_i(C_i+z)-\lambda z$ over $z>-C_i$, and $\sum_iz_i=y$ — if and only if
--   $$\lambda=\lambda^S(y)=\frac{y+C+\sum_i\frac{b_i}{2a_i}}{\sum_i\frac{1}{2a_i}}\qquad\text{and}\qquad z_i=-C_i+\frac{\lambda-b_i}{2a_i}\ \text{for all } i .$$
--
--   This is the inverse demand that a strategic generator faces in the quantity game (56): it is affine and decreasing in the total supply.
--
--   **Formalization Note** The equivalence includes existence and uniqueness of the clearing pair at every $y\ge0$. Assumption 5 includes the readings H1, H2 of its informal clauses; H1 is what keeps every such price below every $b_i$, so that the responses satisfy the open constraint $z_i>-C_i$.
-- source:
--   Gao, Alshehri, Birge, Aggregating Distributed Energy Resources: Efficiency and Market Power, working paper, SSRN abstract 3931052 (PDF of September 26, 2021), §5.1.2, p. 29, (52), (57), (58)

import Mathlib
import Definitions.Def_DERAggregation_MarketPower_Setting

namespace DERAggregation.MarketPower

open Finset

/-- (58), §5.1.2, p. 29. Under Assumption 5, at every total generator supply `y ≥ 0` the pairs
`(λ, z)` clearing the participation market ((52) with (57)) are exactly
`λ = λ^S(y) = (y + C + Σ_i b_i/(2a_i)) / Σ_i 1/(2a_i)` with `z_i = −C_i + (λ − b_i)/(2a_i)`. -/
theorem eq_58 {ι : Type*} [Fintype ι] (a b C : ι → ℝ) (α : ℝ) (N : ℕ)
    (h5 : Assumption5 a b C α N) (y : ℝ) (hy : 0 ≤ y) (lam : ℝ) (z : ι → ℝ) :
    ClearsP a b C y lam z ↔
      (lam = (y + (∑ i, C i) + (∑ i, b i / (2 * a i))) / (∑ i, 1 / (2 * a i)) ∧
        ∀ i, z i = -C i + (lam - b i) / (2 * a i)) := by sorry

end DERAggregation.MarketPower

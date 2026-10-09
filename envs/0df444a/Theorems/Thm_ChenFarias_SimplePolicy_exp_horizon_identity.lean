-- Prove2me | Theorems.Thm_ChenFarias_SimplePolicy_exp_horizon_identity
-- name    : ChenFarias.SimplePolicy.exp_horizon_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:02:46.325154+00:00
-- url     : https://prove2.me/theorems/f88c659b-b41d-4bec-bcf5-ab94f23a3f72
-- title:
--   Proof of Lemma 9, p. 1131 — discounting equals an exponential horizon
-- statement:
--   Let $\lambda>0$ be the customer-arrival rate, $f$ the nonnegative valuation density of total mass one on $[0,\infty)$, $\bar F(p)=\int_p^\infty f(v)\,dv$ its tail, $V$ the discounted Bellman value at rate $\beta>0$, and $\pi$ its unique-root inventory price. Inventory starts at $x_0\in\mathbb N$. Assume the paper’s Assumption 1 and the disclosed full-support condition $f(p)>0$ for $p\ge0$.
--
--   Let $X$ be exponential with rate $\beta$, independent of the sales clocks. The expected discounted revenue equals the expected revenue earned before $X$:
--
--   $$\mathbb E\!\left[\sum_{k=1}^{x_0}e^{-\beta S_k}\pi(x_0-k+1)\right]=\mathbb E_X[J(x_0,X)].$$
--
--   Discounting at rate $\beta$ is the same as stopping the revenue count at an independent exponential time of rate $\beta$. This is the bridge from the infinite-horizon value to finite horizons in the proof of Lemma 9.
--
--   **Formalization Note** Independence is represented by an outer lower integral over $X\sim\operatorname{Exp}(\beta)$ and the inner clock expectation in $J$. The law is parameterized by rate, not mean. The identity uses the same sale-time and revenue definitions as the goal.
-- source:
--   Chen and Farias, Robust Dynamic Pricing with Strategic Customers, Mathematics of Operations Research 43(4) (2018), p. 1131, proof of Lemma 9, first display after first equality

import Mathlib
import Definitions.Def_ChenFarias_SimplePolicy_Model

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ChenFarias.SimplePolicy

/-- The discounted-revenue and independent exponential-horizon identity
in the first display of the proof of Lemma 9. -/
theorem exp_horizon_identity (lam β : ℝ) (f : ℝ → ℝ) (V : ℕ → ℝ)
    (π : ℕ → ℝ) (x0 : ℕ) (hlam : 0 < lam) (hβ : 0 < β)
    (hf : Assumption1 f) (hV : IsValueFn lam β f V)
    (hπ : IsRootPolicy f V π) :
    (∫⁻ e, ENNReal.ofReal (discRevenue lam f π x0 β e) ∂clockLaw x0) =
      ∫⁻ s, J lam f π x0 s ∂expMeasure β := by sorry

end ChenFarias.SimplePolicy

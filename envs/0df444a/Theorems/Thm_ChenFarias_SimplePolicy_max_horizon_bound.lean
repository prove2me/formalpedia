-- Prove2me | Theorems.Thm_ChenFarias_SimplePolicy_max_horizon_bound
-- name    : ChenFarias.SimplePolicy.max_horizon_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:02:54.828402+00:00
-- url     : https://prove2.me/theorems/b2253d2e-2ed9-438a-ad5f-f042183a0e12
-- title:
--   Proof of Lemma 9, p. 1131 — exponential-horizon revenue bound
-- statement:
--   Let $\lambda>0$ be the customer-arrival rate, $f$ the nonnegative valuation density of total mass one on $[0,\infty)$, $\bar F(p)=\int_p^\infty f(v)\,dv$ its tail, $V$ the discounted Bellman value at rate $\beta>0$, and $\pi$ its unique-root inventory price. Inventory starts at $x_0\in\mathbb N$. Assume the paper’s Assumption 1 and the disclosed full-support condition $f(p)>0$ for $p\ge0$.
--
--   For every fixed horizon $T>0$ and independent $X\sim\operatorname{Exp}(\beta)$,
--
--   $$\mathbb E_X[J(x_0,X)]\le\mathbb E[\max\{1,X/T\}]\,J(x_0,T).$$
--
--   Together with the exact evaluation of $\mathbb E[\max\{1,X/T\}]$, it gives Lemma 9.
--
--   **Formalization Note** The paper’s equality immediately after this inequality prints $1+e^{-\beta T}/T$; the missing $\beta$ is corrected in the separate expectation identity. Division by $T$ is legitimate because $T>0$.
-- source:
--   Chen and Farias, Robust Dynamic Pricing with Strategic Customers, Mathematics of Operations Research 43(4) (2018), p. 1131, proof of Lemma 9, second display

import Mathlib
import Definitions.Def_ChenFarias_SimplePolicy_Model

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ChenFarias.SimplePolicy

/-- The second display in the proof of Lemma 9, before evaluating the
expectation of the maximum. -/
theorem max_horizon_bound (lam β T : ℝ) (f : ℝ → ℝ) (V : ℕ → ℝ)
    (π : ℕ → ℝ) (x0 : ℕ) (hlam : 0 < lam) (hβ : 0 < β)
    (hT : 0 < T) (hf : Assumption1 f) (hV : IsValueFn lam β f V)
    (hπ : IsRootPolicy f V π) :
    (∫⁻ s, J lam f π x0 s ∂expMeasure β) ≤
      (∫⁻ s, ENNReal.ofReal (max 1 (s / T)) ∂expMeasure β) *
        J lam f π x0 T := by sorry

end ChenFarias.SimplePolicy

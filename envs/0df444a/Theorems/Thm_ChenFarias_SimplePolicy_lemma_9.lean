-- Prove2me | Theorems.Thm_ChenFarias_SimplePolicy_lemma_9
-- name    : ChenFarias.SimplePolicy.lemma_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:02:50.982487+00:00
-- url     : https://prove2.me/theorems/2f33d6c6-6fcd-40eb-9bfc-4e1c9f531c80
-- title:
--   Lemma 9, p. 1131 — lower bound for the simple robust pricing policy
-- statement:
--   Let $\lambda>0$ be the customer-arrival rate, $f$ the nonnegative valuation density of total mass one on $[0,\infty)$, $\bar F(p)=\int_p^\infty f(v)\,dv$ its tail, $V$ the discounted Bellman value at rate $\beta>0$, and $\pi$ its unique-root inventory price. Inventory starts at $x_0\in\mathbb N$. Assume the paper’s Assumption 1 and the disclosed full-support condition $f(p)>0$ for $p\ge0$.
--
--   For every $\lambda>0$, $\beta>0$, $T>0$ and $x_0\in\mathbb N$, the expected revenue $J(x_0,T)$ that the simple robust pricing policy $\hat\pi^\beta_t=\pi(X_{t-})$ earns over $[0,T]$ satisfies
--
--   $$V(x_0)\le\left(1+\frac{e^{-\beta T}}{\beta T}\right)J(x_0,T).$$
--
--   This is the lower-bound half of Theorem 1 of the paper. Combined with the paper's upper bound $J^*(x_0,T)\le e^{\beta T}V^*_\beta(x_0)$ (Lemma 6, not formalized here), it yields the factor $1/(e^{\beta T}+1/(\beta T))$ of the paper's performance guarantee.
--
--   **Formalization Note** Here $V$ is any solution of the corrected discounted Bellman recursion and $\pi$ is its unique-root policy. Their predicates determine the objects specified by the paper. $J$ is built directly from sales clocks and prices; it is not defined from $V$. The conclusion is in the extended nonnegative reals, with $V(x_0)$ embedded by `ENNReal.ofReal`; the value and all revenues are nonnegative. The paper identifies the strategic-policy revenue with this myopic-sales revenue using its equilibrium claim, which is outside this mission.
-- source:
--   Chen and Farias, Robust Dynamic Pricing with Strategic Customers, Mathematics of Operations Research 43(4) (2018), p. 1131, Lemma 9

import Mathlib
import Definitions.Def_ChenFarias_SimplePolicy_Model

open scoped ENNReal

namespace ChenFarias.SimplePolicy

/-- Lemma 9: the lower-bound half of Theorem 1. -/
theorem lemma_9 (lam β T : ℝ) (x0 : ℕ) (f : ℝ → ℝ)
    (hlam : 0 < lam) (hβ : 0 < β) (hT : 0 < T)
    (hf : Assumption1 f) (V : ℕ → ℝ)
    (hV : IsValueFn lam β f V) (π : ℕ → ℝ)
    (hπ : IsRootPolicy f V π) :
    ENNReal.ofReal (V x0) ≤
      ENNReal.ofReal (1 + Real.exp (-(β * T)) / (β * T)) *
        J lam f π x0 T := by sorry

end ChenFarias.SimplePolicy

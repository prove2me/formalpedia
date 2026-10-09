-- Prove2me | Theorems.Thm_ChenFarias_SimplePolicy_lemma_8
-- name    : ChenFarias.SimplePolicy.lemma_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:02:38.040052+00:00
-- url     : https://prove2.me/theorems/4447d4a3-cfe6-4848-98ab-ba31c02aed29
-- title:
--   Lemma 8, p. 1131 — expected revenue per unit time decreases with horizon
-- statement:
--   Let $\lambda>0$ be the customer-arrival rate, $f$ the nonnegative valuation density of total mass one on $[0,\infty)$, $\bar F(p)=\int_p^\infty f(v)\,dv$ its tail, $V$ the discounted Bellman value at rate $\beta>0$, and $\pi$ its unique-root inventory price. Inventory starts at $x_0\in\mathbb N$. Assume the paper’s Assumption 1 and the disclosed full-support condition $f(p)>0$ for $p\ge0$.
--
--   For $T>T'>0$, the expected revenue per unit time obeys
--
--   $$\frac{J(x_0,T)}{T}\le\frac{J(x_0,T')}{T'}.$$
--
--   Applied at every realization of an independent exponential horizon, it gives the second display in the proof of Lemma 9.
--
--   **Formalization Note** Both ratios are in the extended nonnegative reals; $T,T'>0$ make both denominators nonzero. The revenue is the myopic-sales revenue of the paper’s simple robust policy.
-- source:
--   Chen and Farias, Robust Dynamic Pricing with Strategic Customers, Mathematics of Operations Research 43(4) (2018), p. 1131, Lemma 8

import Mathlib
import Definitions.Def_ChenFarias_SimplePolicy_Model

open scoped ENNReal

namespace ChenFarias.SimplePolicy

/-- Lemma 8: average expected revenue decreases with the horizon. -/
theorem lemma_8 (lam β T T' : ℝ) (f : ℝ → ℝ) (V : ℕ → ℝ)
    (π : ℕ → ℝ) (x0 : ℕ) (hlam : 0 < lam) (hβ : 0 < β)
    (hT' : 0 < T') (hTT' : T' < T) (hf : Assumption1 f)
    (hV : IsValueFn lam β f V) (hπ : IsRootPolicy f V π) :
    J lam f π x0 T / ENNReal.ofReal T ≤
      J lam f π x0 T' / ENNReal.ofReal T' := by sorry

end ChenFarias.SimplePolicy

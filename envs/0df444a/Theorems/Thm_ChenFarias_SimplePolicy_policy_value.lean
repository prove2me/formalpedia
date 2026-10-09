-- Prove2me | Theorems.Thm_ChenFarias_SimplePolicy_policy_value
-- name    : ChenFarias.SimplePolicy.policy_value
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:02:44.743329+00:00
-- url     : https://prove2.me/theorems/eed74f6e-b35e-4686-abe3-27815951f118
-- title:
--   Proof of Lemma 9, p. 1131 — Bellman value equals discounted policy revenue
-- statement:
--   Let $\lambda>0$ be the customer-arrival rate, $f$ the nonnegative valuation density of total mass one on $[0,\infty)$, $\bar F(p)=\int_p^\infty f(v)\,dv$ its tail, $V$ the discounted Bellman value at rate $\beta>0$, and $\pi$ its unique-root inventory price. Inventory starts at $x_0\in\mathbb N$. Assume the paper’s Assumption 1 and the disclosed full-support condition $f(p)>0$ for $p\ge0$.
--
--   The solution of the corrected Bellman recursion equals the expected infinite-horizon discounted revenue earned by its root policy:
--
--   $$V(x_0)=\mathbb E\!\left[\sum_{k=1}^{x_0}e^{-\beta S_k}\pi(x_0-k+1)\right],$$
--
--   where $S_k$ is the time of sale $k$.
--
--   It ties the Bellman value, defined by an optimization equation, to the revenue of the concrete sales process. It is the first equality in the proof of Lemma 9.
--
--   **Formalization Note** This is a substantive verification theorem: $V$ is specified by the Bellman recursion, not by the revenue sum. The nonnegative real value is injected into the extended nonnegative reals on the left. The discounted sum is nonnegative because every charged price is nonnegative.
-- source:
--   Chen and Farias, Robust Dynamic Pricing with Strategic Customers, Mathematics of Operations Research 43(4) (2018), p. 1131, proof of Lemma 9, first equality

import Mathlib
import Definitions.Def_ChenFarias_SimplePolicy_Model

open MeasureTheory
open scoped ENNReal

namespace ChenFarias.SimplePolicy

/-- First equality in the proof of Lemma 9: Bellman value equals the
discounted revenue of its unique-root stationary policy. -/
theorem policy_value (lam β : ℝ) (f : ℝ → ℝ) (V : ℕ → ℝ)
    (π : ℕ → ℝ) (x0 : ℕ) (hlam : 0 < lam) (hβ : 0 < β)
    (hf : Assumption1 f) (hV : IsValueFn lam β f V)
    (hπ : IsRootPolicy f V π) :
    ENNReal.ofReal (V x0) =
      ∫⁻ e, ENNReal.ofReal (discRevenue lam f π x0 β e) ∂clockLaw x0 := by sorry

end ChenFarias.SimplePolicy

-- Prove2me | Theorems.Thm_ChenFarias_SimplePolicy_price_antitone
-- name    : ChenFarias.SimplePolicy.price_antitone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:02:43.350984+00:00
-- url     : https://prove2.me/theorems/de2a348e-9a6c-4b01-9305-36f369b0a7c7
-- title:
--   §3.1, item 1, p. 1125 — optimal root price is nonincreasing in inventory
-- statement:
--   Let $\lambda>0$ be the customer-arrival rate, $f$ the nonnegative valuation density of total mass one on $[0,\infty)$, $\bar F(p)=\int_p^\infty f(v)\,dv$ its tail, $V$ the discounted Bellman value at rate $\beta>0$, and $\pi$ its unique-root inventory price. Assume the paper’s Assumption 1 and the disclosed full-support condition $f(p)>0$ for $p\ge0$.
--
--   For inventory levels $1\le x\le y$, the root prices satisfy
--
--   $$\pi(y)\le\pi(x).$$
--
--   Since inventory only falls, this makes the posted price $\hat\pi^\beta_t=\pi(X_{t-})$ nondecreasing in time whatever the customers do (§3.1, item 1). It is the first claim of Lemma 7.
--
--   **Formalization Note** “Decreasing” on the page is read as nonincreasing. Only positive inventory is priced; the zero-inventory price is represented separately as infinity. The root predicate includes uniqueness as disclosed in the model.
-- source:
--   Chen and Farias, Robust Dynamic Pricing with Strategic Customers, Mathematics of Operations Research 43(4) (2018), p. 1125, §3.1, item 1

import Mathlib
import Definitions.Def_ChenFarias_SimplePolicy_Model

namespace ChenFarias.SimplePolicy

/-- Section 3.1, item 1: the root price decreases with inventory. -/
theorem price_antitone (lam β : ℝ) (f : ℝ → ℝ) (V : ℕ → ℝ) (π : ℕ → ℝ)
    (hlam : 0 < lam) (hβ : 0 < β) (hf : Assumption1 f)
    (hV : IsValueFn lam β f V) (hπ : IsRootPolicy f V π) :
    AntitoneOn π (Set.Ici 1) := by sorry

end ChenFarias.SimplePolicy

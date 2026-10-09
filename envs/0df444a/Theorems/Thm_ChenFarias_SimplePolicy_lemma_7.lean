-- Prove2me | Theorems.Thm_ChenFarias_SimplePolicy_lemma_7
-- name    : ChenFarias.SimplePolicy.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:02:35.186331+00:00
-- url     : https://prove2.me/theorems/f2f3cc4f-a153-425e-a257-8e9f1de5e0c0
-- title:
--   Lemma 7, p. 1130 — prices rise and revenue rates fall on every path
-- statement:
--   Let $\lambda>0$ be the customer-arrival rate, $f$ the nonnegative valuation density of total mass one on $[0,\infty)$, $\bar F(p)=\int_p^\infty f(v)\,dv$ its tail, $V$ the discounted Bellman value at rate $\beta>0$, and $\pi$ its unique-root inventory price. Inventory starts at $x_0\in\mathbb N$. Assume the paper’s Assumption 1 and the disclosed full-support condition $f(p)>0$ for $p\ge0$.
--
--   For every realization of the exponential clocks and every $s\le t$, the posted price is nondecreasing and the sale-revenue rate is nonincreasing:
--
--   $$\hat\pi_s^\beta\le\hat\pi_t^\beta,\qquad \hat\pi_t^\beta\bar F(\hat\pi_t^\beta)\le \hat\pi_s^\beta\bar F(\hat\pi_s^\beta).$$
--
--   Lemma 8 integrates the second claim over time.
--
--   **Formalization Note** This quantifies over every real clock vector, including vectors outside the support of the exponential law, as “every sample path” requires. At sell-out the first price is infinity and the second rate is zero. Time is all real numbers; on valid nonnegative-clock paths, the process has initial inventory until time zero.
-- source:
--   Chen and Farias, Robust Dynamic Pricing with Strategic Customers, Mathematics of Operations Research 43(4) (2018), p. 1130, Lemma 7

import Mathlib
import Definitions.Def_ChenFarias_SimplePolicy_Model

namespace ChenFarias.SimplePolicy

/-- Lemma 7, including the infinite posted price and zero revenue rate after sell-out. -/
theorem lemma_7 (lam β : ℝ) (f : ℝ → ℝ) (V : ℕ → ℝ) (π : ℕ → ℝ)
    (x0 : ℕ) (hlam : 0 < lam) (hβ : 0 < β) (hf : Assumption1 f)
    (hV : IsValueFn lam β f V) (hπ : IsRootPolicy f V π) :
    ∀ (e : Fin x0 → ℝ) (s t : ℝ), s ≤ t →
      priceAt lam f π x0 e s ≤ priceAt lam f π x0 e t ∧
      rateRev f π (Xminus lam f π x0 e t) ≤
        rateRev f π (Xminus lam f π x0 e s) := by sorry

end ChenFarias.SimplePolicy

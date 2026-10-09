-- Prove2me | Theorems.Thm_ChenFarias_SimplePolicy_value_monotone
-- name    : ChenFarias.SimplePolicy.value_monotone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:02:41.133675+00:00
-- url     : https://prove2.me/theorems/4996589c-002b-4a50-bd5a-ca3cbbdc14ad
-- title:
--   Proof of Lemma 7, p. 1131 — Bellman value increases with inventory
-- statement:
--   Let $\lambda,\beta>0$, let $f$ be a valuation density satisfying the paper’s Assumption 1 and the disclosed full-support condition, and let $V$ solve the corrected discounted Bellman recursion.
--
--   For every positive inventory level $x$, the discounted value is nondecreasing:
--
--   $$V(x-1)\le V(x).$$
--
--   Nonnegative marginal values $V(x)-V(x-1)$ place every root price where $\psi\ge0$; the proof of Lemma 7 uses this to show that the posted price stays above the root $v^*$ of $\psi$.
--
--   **Formalization Note** The statement uses the corrected Bellman recursion. The hypothesis $x\ge1$ makes natural-number subtraction exact. No lower bound on $x_0$ is needed here.
-- source:
--   Chen and Farias, Robust Dynamic Pricing with Strategic Customers, Mathematics of Operations Research 43(4) (2018), p. 1131, proof of Lemma 7

import Mathlib
import Definitions.Def_ChenFarias_SimplePolicy_Model

namespace ChenFarias.SimplePolicy

/-- The inventory monotonicity used in the proof of Lemma 7. -/
theorem value_monotone (lam β : ℝ) (f : ℝ → ℝ) (V : ℕ → ℝ)
    (hlam : 0 < lam) (hβ : 0 < β) (hf : Assumption1 f)
    (hV : IsValueFn lam β f V) :
    ∀ x : ℕ, 1 ≤ x → V (x - 1) ≤ V x := by sorry

end ChenFarias.SimplePolicy

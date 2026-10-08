-- Prove2me | Theorems.Thm_AsyncSA_Monotone_lemma5
-- name    : AsyncSA.Monotone.lemma5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:55:57.976762+00:00
-- url     : https://prove2.me/theorems/204b82a7-348d-420d-9683-6e25c93e005f
-- title:
--   Lemma 5 — the sequences U^k and L^k converge to x*
-- statement:
--   Let $F:\mathbb R^n\to\mathbb R^n$ satisfy Assumption 4 with unique fixed point $x^*$ (monotone, continuous, unique fixed point, and $F(x)-re\le F(x-re)\le F(x+re)\le F(x)+re$ for all $x$ and all $r>0$). Fix $r>0$ and let $U^k,L^k$ be defined by $U^0=x^*+re$, $L^0=x^*-re$ and
--   $$
--   U^{k+1}=\frac{U^k+F(U^k)}{2},\qquad L^{k+1}=\frac{L^k+F(L^k)}{2}.
--   $$
--   Then
--   $$
--   \lim_{k\to\infty}U^k=x^*\qquad\text{and}\qquad\lim_{k\to\infty}L^k=x^* .
--   $$
--
--   Together with the bracketing $L^k\le x(t)\le U^k$ for large $t$, this is what turns the envelope argument of §5 into convergence of $x(t)$ to $x^*$.
--
--   **Formalization Note** Convergence is in $\mathbb R^n$ (`Fin n → ℝ` with its product topology, equivalently the maximum norm). The statement holds for every $r>0$, as in Lemma 4.
-- source:
--   Tsitsiklis, Asynchronous Stochastic Approximation and Q-Learning, Machine Learning 16 (1994), p. 193, §5, Lemma 5

import Mathlib
import Definitions.Def_AsyncSA_Monotone_Model

namespace AsyncSA.Monotone

open Filter Topology

theorem lemma5 {n : ℕ} (F : (Fin n → ℝ) → Fin n → ℝ) (xstar : Fin n → ℝ) (r : ℝ)
    (h4 : Assumption4 F xstar) (hr : 0 < r) :
    Tendsto (Useq F xstar r) atTop (𝓝 xstar) ∧ Tendsto (Lseq F xstar r) atTop (𝓝 xstar) := by sorry

end AsyncSA.Monotone

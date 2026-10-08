-- Prove2me | Theorems.Thm_AsyncSA_Monotone_lemma4
-- name    : AsyncSA.Monotone.lemma4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:55:51.32873+00:00
-- url     : https://prove2.me/theorems/3f93a13e-50ed-459f-bf7a-4d9bb850244a
-- title:
--   Lemma 4 — F(U^k) ≤ U^{k+1} ≤ U^k and F(L^k) ≥ L^{k+1} ≥ L^k
-- statement:
--   Let $F:\mathbb R^n\to\mathbb R^n$ satisfy Assumption 4 with unique fixed point $x^*$: $F$ is monotone and continuous, $x^*$ is its only fixed point, and $F(x)-re\le F(x-re)\le F(x+re)\le F(x)+re$ for all $x$ and all $r>0$, where $e$ is the vector of ones and inequalities between vectors are componentwise. Fix $r>0$ and define
--   $$
--   U^0=x^*+re,\quad L^0=x^*-re,\qquad U^{k+1}=\frac{U^k+F(U^k)}{2},\quad L^{k+1}=\frac{L^k+F(L^k)}{2}\quad(k\ge0).
--   $$
--   Then for every $k\ge0$,
--   $$
--   F(U^k)\le U^{k+1}\le U^k\qquad\text{and}\qquad F(L^k)\ge L^{k+1}\ge L^k .
--   $$
--
--   So $\{U^k\}$ is nonincreasing and $\{L^k\}$ nondecreasing; these sequences are the upper and lower envelopes that trap the iterates $x(t)$ in the proof of Theorem 2.
--
--   **Formalization Note** The paper takes $r$ large enough that $x^*-re\le x(t)\le x^*+re$ for all $t$; the lemma itself holds for every $r>0$ and is stated that way. $re$ is `r • 1`, and the vector inequalities are the componentwise order on `Fin n → ℝ`. The hypothesis is the whole of Assumption 4, as in the paper.
-- source:
--   Tsitsiklis, Asynchronous Stochastic Approximation and Q-Learning, Machine Learning 16 (1994), p. 193, §5, Lemma 4 (with (16), (17))

import Mathlib
import Definitions.Def_AsyncSA_Monotone_Model

namespace AsyncSA.Monotone

theorem lemma4 {n : ℕ} (F : (Fin n → ℝ) → Fin n → ℝ) (xstar : Fin n → ℝ) (r : ℝ)
    (h4 : Assumption4 F xstar) (hr : 0 < r) (k : ℕ) :
    (F (Useq F xstar r k) ≤ Useq F xstar r (k + 1) ∧
        Useq F xstar r (k + 1) ≤ Useq F xstar r k) ∧
      (Lseq F xstar r (k + 1) ≤ F (Lseq F xstar r k) ∧
        Lseq F xstar r k ≤ Lseq F xstar r (k + 1)) := by sorry

end AsyncSA.Monotone

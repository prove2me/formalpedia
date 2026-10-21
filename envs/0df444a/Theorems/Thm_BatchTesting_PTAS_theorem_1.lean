-- Prove2me | Theorems.Thm_BatchTesting_PTAS_theorem_1
-- name    : BatchTesting.PTAS.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:49:56.200979+00:00
-- url     : https://prove2.me/theorems/c3319cdc-9f4f-4213-9414-c7bc0e62d515
-- title:
--   Theorem 1, p. 6 — an optimal path of the DP over great-looking states gives a testing scheme within $(1+\epsilon)K(\epsilon)$ of optimal, over an explicitly bounded state space
-- statement:
--   Let $X_1,\dots,X_n$ ($n\ge1$) be independent Bernoulli variables with $\Pr[X_i=1]=p_i\in[0,1]$, testing costs $c_i>0$ and set-up cost $\beta\ge0$, and let $0<\epsilon\le1$. Run the algorithm of the paper: normalize the costs by $c_{\min}$, round them up to powers of $1+\epsilon$, and solve the dynamic program over the great-looking states $F_{\mathrm{great}}$. Then:
--
--   1. the dynamic program over $F_{\mathrm{great}}$ has an optimal path;
--   2. for every optimal path $\pi$, its testing scheme $S_\pi$ is a testing scheme of $[n]$, and for every testing scheme $S$, with the original costs,
--   $$E(S_\pi)\ \le\ (1+\epsilon)\cdot K(\epsilon)\cdot E(S),\qquad K(\epsilon)=(1+3\epsilon)(1+\epsilon)^2+2\epsilon(1+\epsilon)^4;$$
--   3. the state space is small:
--   $$|F_{\mathrm{great}}|\ \le\ (n+1)\cdot\big(R+\lceil\log_{1+\epsilon}n\rceil+1\big)\cdot\binom{\lfloor3\kappa/\epsilon^2\rfloor+\kappa}{\kappa},\qquad\kappa=\lceil\log_{1+\epsilon}(n/\epsilon)\rceil.$$
--
--   This is the paper's main result: sequential batch testing of series systems admits a polynomial-time approximation scheme, improving the earlier $6.829+\epsilon$ guarantee.
--
--   **Formalization Note.** The factor $(1+\epsilon)K(\epsilon)$ is the rounding factor $1+\epsilon$ times Theorem 3's explicit $1+O(\epsilon)$; it is $1+O(\epsilon)$, and the paper's "within factor $1+\epsilon$" follows by running the algorithm with a smaller $\epsilon$. The running time $O((|I|/\epsilon)^{O(1/\epsilon^3)})$ is not formalized; the explicit state count in part 3 stands in for it. "There is a scheme within $1+\epsilon$ of optimal" would be trivially true (an optimal scheme exists), so the statement is about the output of the algorithm, compared with the original costs. Added hypotheses: $n\ge1$, $p_i\in[0,1]$, $\beta\ge0$, $\epsilon\le1$.
-- source:
--   Segev & Shaposhnik, A Polynomial-Time Approximation Scheme for Sequential Batch Testing of Series Systems, SSRN preprint 3277805 (Nov. 2018), p. 6, §1.2, Theorem 1 (proof: §2–§4, pp. 8–24; state count pp. 16–17)

import Mathlib
import Definitions.Def_BatchTesting_PTAS_Model

namespace BatchTesting.PTAS

theorem theorem_1 {n : ℕ} (I : Instance n) (hI : I.Standing) (eps : ℝ) (h0 : 0 < eps) (h1 : eps ≤ 1) :
    (∃ π, IsOptPath I eps (FGreat I eps) π) ∧
      (∀ π, IsOptPath I eps (FGreat I eps) π →
        IsTestingScheme (schemeOf I eps π) ∧
          ∀ S, IsTestingScheme S →
            expectedCost I (schemeOf I eps π) ≤ (1 + eps) * K eps * expectedCost I S) ∧
      (FGreat I eps).card ≤ (n + 1) * (R I eps + ⌈Real.logb (1 + eps) (n : ℝ)⌉₊ + 1) *
        Nat.choose (⌊3 * (kappa n eps : ℝ) / eps ^ 2⌋₊ + (kappa n eps).toNat) (kappa n eps).toNat := by sorry

end BatchTesting.PTAS

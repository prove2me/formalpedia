-- Prove2me | Theorems.Thm_EthierKurtz_cramer_weighted_rademacher_sums
-- name    : EthierKurtz.cramer_weighted_rademacher_sums
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-26T23:55:34.876016+00:00
-- url     : https://prove2.me/theorems/f09e8b76-7796-472a-809a-91bbfbd9e317
-- title:
--   Cramér-type bound for weighted Rademacher sums (KMT Lemma B)
-- statement:
--   Let $M,b>0$. There are $\varepsilon,C>0$ and $N_0$ such that for every $N\ge1$ with $N\ge N_0$, every $d\in\mathbb R^N$ with $|d_i|\le M$ and $\sum_id_i^2\ge bN$, and every $0\le y\le\varepsilon\sqrt N$, the proportion $p$ of sign vectors $r\in\{\pm1\}^N$ with $\sum_i r_id_i>y\sqrt N$ satisfies
--
--   $$\Big(1-\Phi\Big(\frac{y\sqrt N}{\sqrt{\sum_id_i^2}}\Big)\Big)e^{-C(y^3+1)/\sqrt N}\le p\le\Big(1-\Phi\Big(\frac{y\sqrt N}{\sqrt{\sum_id_i^2}}\Big)\Big)e^{C(y^3+1)/\sqrt N}.$$
--
--   Role: Lemma B of KMT II for the variables $\xi_i=r_id_i$, the conditional estimate in the proof of Lemma 3.
-- source:
--   J. Komlós, P. Major, G. Tusnády, An approximation of partial sums of independent RV's and the sample DF. II, Z. Wahrsch. verw. Gebiete 34 (1976) 33-58, https://static.renyi.hu/~major/articles/KMT2.pdf, Lemma B, pp. 41-42, applied to $\xi_i=(x_{\pi(i)}-x_{\pi(N+i)})r_i$ as on p. 42

import Mathlib

namespace EthierKurtz

theorem cramer_weighted_rademacher_sums :
    ∀ (M b : ℝ),
      (0 : ℝ) < M →
        (0 : ℝ) < b →
          ∃ (ε : ℝ) (C : ℝ) (N0 : ℝ),
            (0 : ℝ) < ε ∧
              (0 : ℝ) < C ∧
                ∀ (N : ℕ),
                  (1 : ℕ) ≤ N →
                    N0 ≤ ↑N →
                      ∀ (d : Fin N → ℝ),
                        (∀ (i : Fin N), |d i| ≤ M) →
                          b * ↑N ≤ ∑ i : Fin N, d i ^ (2 : ℕ) →
                            ∀ (y : ℝ),
                              (0 : ℝ) ≤ y →
                                y ≤ ε * √↑N →
                                  ((1 : ℝ) -
                                          (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal)))
                                            (y * √↑N / √(∑ i : Fin N, d i ^ (2 : ℕ)))) *
                                        Real.exp (-(C * ((y ^ (3 : ℕ) + (1 : ℝ)) / √↑N))) ≤
                                      ↑(Finset.card
                                            {e : Fin N → Bool |
                                              y * √↑N <
                                                ∑ i : Fin N, (if e i = Bool.true then (-1 : ℝ) else (1 : ℝ)) * d i}) /
                                        (2 : ℝ) ^ N ∧
                                    ↑(Finset.card
                                            {e : Fin N → Bool |
                                              y * √↑N <
                                                ∑ i : Fin N, (if e i = Bool.true then (-1 : ℝ) else (1 : ℝ)) * d i}) /
                                        (2 : ℝ) ^ N ≤
                                      ((1 : ℝ) -
                                          (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal)))
                                            (y * √↑N / √(∑ i : Fin N, d i ^ (2 : ℕ)))) *
                                        Real.exp (C * ((y ^ (3 : ℕ) + (1 : ℝ)) / √↑N)) := by sorry

end EthierKurtz

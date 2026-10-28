-- Prove2me | Theorems.Thm_EthierKurtz_kmt_permutation_conditional_quantile_bound
-- name    : EthierKurtz.kmt_permutation_conditional_quantile_bound
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-26T23:45:11.105882+00:00
-- url     : https://prove2.me/theorems/3d6f6312-6c47-4e0f-9854-f460c6a727f0
-- title:
--   KMT node estimate (4.12) for random half-splits
-- statement:
--   Let $K>0$. There are $C>0$, $0<\varepsilon\le1/4$ and $N_1\ge1$ such that the following holds for every $N\ge N_1$. Let $y\in\mathbb R^{2N}$ (indexed by two copies of $\{1,\dots,N\}$) with $|y_i|\le K$, $|\sum_i y_i|\le\varepsilon\,2N$ and $|\sum_i(y_i^2-1)|\le\varepsilon\,2N$. Let $G$ be the distribution function of $D_\pi=\sum_{i=1}^N(y_{\pi(i)}-y_{\pi(N+i)})$ for a uniform random permutation $\pi$ of the $2N$ indices, and $G^{-1}(t)=\inf\{x:t\le G(x)\}$. Then for every $|v|<\varepsilon\,2N$
--
--   $$\Big|G^{-1}\big(\Phi(v/\sqrt{2N})\big)-v\Big|\le C\Big(1+\frac{v^2}{2N}+\frac{(\sum_iy_i)^2}{2N}+\frac{(\sum_i(y_i^2-1))^2}{2N}\Big).$$
--
--   Role: The node step of the dyadic construction: the conditional quantile transform given the multiset of block values moves the normal increment by at most the bound (4.12) under (4.13).
-- source:
--   J. Komlós, P. Major, G. Tusnády, An approximation of partial sums of independent RV's and the sample DF. II, Z. Wahrsch. verw. Gebiete 34 (1976) 33-58, https://static.renyi.hu/~major/articles/KMT2.pdf, Section 4, formulas (4.12)-(4.13) and the halving construction, pp. 48-49

import Mathlib

namespace EthierKurtz

theorem kmt_permutation_conditional_quantile_bound :
    ∀ (K : ℝ),
      (0 : ℝ) < K →
        ∃ (C : ℝ) (ε : ℝ) (N1 : ℕ),
          (0 : ℝ) < C ∧
            (0 : ℝ) < ε ∧
              ε ≤ (1 / 4 : ℝ) ∧
                (1 : ℕ) ≤ N1 ∧
                  ∀ (N : ℕ),
                    N1 ≤ N →
                      ∀ (y : Fin N ⊕ Fin N → ℝ),
                        (∀ (i : Fin N ⊕ Fin N), |y i| ≤ K) →
                          |∑ i : Fin N ⊕ Fin N, y i| ≤ ε * ↑((2 : ℕ) * N) →
                            |∑ i : Fin N ⊕ Fin N, (y i ^ (2 : ℕ) - (1 : ℝ))| ≤ ε * ↑((2 : ℕ) * N) →
                              ∀ (v : ℝ),
                                |v| < ε * ↑((2 : ℕ) * N) →
                                  |InfSet.sInf
                                          {x : ℝ |
                                            (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal)))
                                                (v / √↑((2 : ℕ) * N)) ≤
                                              (ProbabilityTheory.cdf
                                                    (((Fintype.card (Equiv.Perm (Fin N ⊕ Fin N)) : ENNReal))⁻¹ •
                                                      ∑ w : Equiv.Perm (Fin N ⊕ Fin N),
                                                        MeasureTheory.Measure.dirac
                                                          (∑ i : Fin N, (y (w (Sum.inl i)) - y (w (Sum.inr i))))))
                                                x} -
                                        v| ≤
                                    C *
                                      ((1 : ℝ) + v ^ (2 : ℕ) / ↑((2 : ℕ) * N) +
                                          (∑ i : Fin N ⊕ Fin N, y i) ^ (2 : ℕ) / ↑((2 : ℕ) * N) +
                                        (∑ i : Fin N ⊕ Fin N, (y i ^ (2 : ℕ) - (1 : ℝ))) ^ (2 : ℕ) / ↑((2 : ℕ) * N)) := by sorry

end EthierKurtz

-- Prove2me | Theorems.Thm_EthierKurtz_kmt_finite_population_cramer_average
-- name    : EthierKurtz.kmt_finite_population_cramer_average
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-27T00:07:18.746991+00:00
-- url     : https://prove2.me/theorems/524c4f34-f2b5-469d-8f1b-c003172cfa88
-- title:
--   Averaging the conditional Cramér bound over permutations (KMT (4.2))
-- statement:
--   Let $K,c>0$. There are $0<\varepsilon\le1$, $C>0$ and $N_0$ such that for every $N\ge1$ with $N\ge N_0$, every $x\in\mathbb R^{2N}$ with $|x_i|\le K$, $\sum_ix_i=0$, $\sigma^2=\sum_ix_i^2\ge cN$, and every $0\le y\le\varepsilon\sqrt N$, writing $\sigma_\pi^2=\sum_{i=1}^N(x_{\pi(i)}-x_{\pi(N+i)})^2$ for permutations $\pi$ of the $2N$ indices, $\Psi(s)=1-\Phi(y/\sqrt{s/N})$ and $\mathcal G=\{\pi:\sigma_\pi^2/N\ge c/2\}$:
--
--   $$(2N)!\,\Psi(\sigma^2)e^{-C(y^3+1)/\sqrt N}\le\sum_{\pi\in\mathcal G}\Psi(\sigma_\pi^2)\le(2N)!\,\Psi(\sigma^2)e^{C(y^3+1)/\sqrt N},\qquad\#\{\pi\notin\mathcal G\}\le(2N)!\,\Psi(\sigma^2)/\sqrt N.$$
--
--   Role: The averaging step (4.2)-(4.8) that turns the conditional (given $\pi$) Cramér bound into Lemma 3, the finite-population Cramér estimate for random half-sample sums.
-- source:
--   J. Komlós, P. Major, G. Tusnády, An approximation of partial sums of independent RV's and the sample DF. II, Z. Wahrsch. verw. Gebiete 34 (1976) 33-58, https://static.renyi.hu/~major/articles/KMT2.pdf, proof of Lemma 3, formulas (4.2)-(4.8), pp. 42-44

import Mathlib

namespace EthierKurtz

theorem kmt_finite_population_cramer_average :
    ∀ (K c : ℝ),
      (0 : ℝ) < K →
        (0 : ℝ) < c →
          ∃ (ε : ℝ) (C : ℝ) (N0 : ℝ),
            (0 : ℝ) < ε ∧
              ε ≤ (1 : ℝ) ∧
                (0 : ℝ) < C ∧
                  ∀ (N : ℕ),
                    (1 : ℕ) ≤ N →
                      N0 ≤ ↑N →
                        ∀ (x : Fin N ⊕ Fin N → ℝ),
                          (∀ (i : Fin N ⊕ Fin N), |x i| ≤ K) →
                            ∑ i : Fin N ⊕ Fin N, x i = (0 : ℝ) →
                              c * ↑N ≤ ∑ i : Fin N ⊕ Fin N, x i ^ (2 : ℕ) →
                                ∀ (y : ℝ),
                                  (0 : ℝ) ≤ y →
                                    y ≤ ε * √↑N →
                                      ∑ w : Equiv.Perm (Fin N ⊕ Fin N) with
                                            c / (2 : ℝ) ≤
                                              (∑ i : Fin N, (x (w (Sum.inl i)) - x (w (Sum.inr i))) ^ (2 : ℕ)) / ↑N,
                                            ((1 : ℝ) -
                                              (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal)))
                                                (y /
                                                  √((∑ i : Fin N, (x (w (Sum.inl i)) - x (w (Sum.inr i))) ^ (2 : ℕ)) /
                                                      ↑N))) ≤
                                          ↑(Fintype.card (Equiv.Perm (Fin N ⊕ Fin N))) *
                                              ((1 : ℝ) -
                                                (ProbabilityTheory.cdf
                                                      (ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal)))
                                                  (y / √((∑ i : Fin N ⊕ Fin N, x i ^ (2 : ℕ)) / ↑N))) *
                                            Real.exp (C * ((y ^ (3 : ℕ) + (1 : ℝ)) / √↑N)) ∧
                                        ↑(Finset.card
                                                {w : Equiv.Perm (Fin N ⊕ Fin N) |
                                                  ¬c / (2 : ℝ) ≤
                                                      (∑ i : Fin N, (x (w (Sum.inl i)) - x (w (Sum.inr i))) ^ (2 : ℕ)) /
                                                        ↑N}) ≤
                                            ↑(Fintype.card (Equiv.Perm (Fin N ⊕ Fin N))) *
                                                ((1 : ℝ) -
                                                  (ProbabilityTheory.cdf
                                                        (ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal)))
                                                    (y / √((∑ i : Fin N ⊕ Fin N, x i ^ (2 : ℕ)) / ↑N))) /
                                              √↑N ∧
                                          ↑(Fintype.card (Equiv.Perm (Fin N ⊕ Fin N))) *
                                                ((1 : ℝ) -
                                                  (ProbabilityTheory.cdf
                                                        (ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal)))
                                                    (y / √((∑ i : Fin N ⊕ Fin N, x i ^ (2 : ℕ)) / ↑N))) *
                                              Real.exp (-(C * ((y ^ (3 : ℕ) + (1 : ℝ)) / √↑N))) ≤
                                            ∑ w : Equiv.Perm (Fin N ⊕ Fin N) with
                                              c / (2 : ℝ) ≤
                                                (∑ i : Fin N, (x (w (Sum.inl i)) - x (w (Sum.inr i))) ^ (2 : ℕ)) / ↑N,
                                              ((1 : ℝ) -
                                                (ProbabilityTheory.cdf
                                                      (ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal)))
                                                  (y /
                                                    √((∑ i : Fin N, (x (w (Sum.inl i)) - x (w (Sum.inr i))) ^ (2 : ℕ)) /
                                                        ↑N))) := by sorry

end EthierKurtz

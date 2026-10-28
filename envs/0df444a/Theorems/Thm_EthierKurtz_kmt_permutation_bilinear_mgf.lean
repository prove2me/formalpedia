-- Prove2me | Theorems.Thm_EthierKurtz_kmt_permutation_bilinear_mgf
-- name    : EthierKurtz.kmt_permutation_bilinear_mgf
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-27T00:20:05.02177+00:00
-- url     : https://prove2.me/theorems/1df077b2-6edb-4bce-bb92-69af71420fbc
-- title:
--   Exponential moment of the permutation bilinear form (KMT (4.9))
-- statement:
--   Let $N\ge1$, $K>0$ and $x\in\mathbb R^{2N}$ with $|x_i|\le K$ and $\sum_ix_i=0$. For a permutation $\pi$ of the $2N$ indices put $\eta_\pi=-\frac1{\sqrt N}\sum_{i=1}^Nx_{\pi(i)}x_{\pi(N+i)}$. Then for every $t$ with $1\le|t|\sqrt N$ and $16K^2|t|\le\sqrt N$
--
--   $$\sum_\pi e^{t\eta_\pi}\le(2N)!\,e^{(2K^2+4K^4)t^2}.$$
--
--   Role: The exponential moment bound for the fluctuation of $\sigma_\pi^2$ around $\sigma^2$ used in the averaging step of Lemma 3.
-- source:
--   J. Komlós, P. Major, G. Tusnády, An approximation of partial sums of independent RV's and the sample DF. II, Z. Wahrsch. verw. Gebiete 34 (1976) 33-58, https://static.renyi.hu/~major/articles/KMT2.pdf, formula (4.9), p. 44, with Lemmas 4-5, pp. 45-47

import Mathlib

namespace EthierKurtz

theorem kmt_permutation_bilinear_mgf :
    ∀ {N : ℕ},
      (1 : ℕ) ≤ N →
        ∀ (x : Fin N ⊕ Fin N → ℝ) {K : ℝ},
          (0 : ℝ) < K →
            (∀ (i : Fin N ⊕ Fin N), |x i| ≤ K) →
              ∑ i : Fin N ⊕ Fin N, x i = (0 : ℝ) →
                ∀ (t : ℝ),
                  (1 : ℝ) ≤ |t| * √↑N →
                    |t| * ((16 : ℝ) * K ^ (2 : ℕ)) ≤ √↑N →
                      ∑ w : Equiv.Perm (Fin N ⊕ Fin N),
                          Real.exp (t * (-((1 : ℝ) / √↑N) * ∑ i : Fin N, x (w (Sum.inl i)) * x (w (Sum.inr i)))) ≤
                        ↑(Fintype.card (Equiv.Perm (Fin N ⊕ Fin N))) *
                          Real.exp (((2 : ℝ) * K ^ (2 : ℕ) + (4 : ℝ) * K ^ (4 : ℕ)) * t ^ (2 : ℕ)) := by sorry

end EthierKurtz

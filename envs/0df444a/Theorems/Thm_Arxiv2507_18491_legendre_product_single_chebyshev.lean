-- Prove2me | Theorems.Thm_Arxiv2507_18491_legendre_product_single_chebyshev
-- name    : Arxiv2507_18491.legendre_product_single_chebyshev
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-26T13:05:19.564821+00:00
-- url     : https://prove2.me/theorems/23395a3d-325d-421f-8b00-d99be80c98f7
-- title:
--   Eqs. (3.50)-(3.51): expansion of the Legendre product in Chebyshev polynomials of one argument (as proved)
-- statement:
--   Let $k,k'>0$ and $k_\rho\ge0$. Let $\beta,\beta'$ satisfy $\sin\beta=k_\rho/k$, $\cos\beta=k_z/k$, $\sin\beta'=k_\rho/k'$ and $\cos\beta'=k'_z/k'$, and suppose the expansions (B.3) of $\widehat P_n^m(\cos\beta)$ and $\widehat P_\nu^\mu(\cos\beta')$ hold, as in eq. (3.49), with $|m|\le n$, $|\mu|\le\nu$. Write $Q=\widehat P_n^m(\cos\beta)\widehat P_\nu^\mu(\cos\beta')$ and $\Pi=\frac{s_{m\mu}}2\tau_{n,|m|}(\beta)\tau_{\nu,|\mu|}(\beta')$.
--
--   1. (eq. 3.50) If $k\le k'$, then with $a=(k/k')^2$, $b=1-a$ and $l_0=i-\min(i,j)$,
--   $$Q=\Pi\sum_{i=0}^{K_n}\sum_{j=0}^{K_\nu}B^i_{n,|m|}B^j_{\nu,|\mu|}\Big(\sum_{l=i}^{j+i}C^{ab}_{j,l-i}T_l(\cos2\beta)+\sum_{l=l_0}^{i}C^{ab}_{j,i-l}T_l(\cos2\beta)+\sum_{l=1}^{j-i}C^{ab}_{j,l+i}T_l(\cos2\beta)\Big).$$
--   2. (eq. 3.51) If $k>k'$, then with $a=(k'/k)^2$, $b=1-a$ and $l_0=j-\min(i,j)$,
--   $$Q=\Pi\sum_{i=0}^{K_n}\sum_{j=0}^{K_\nu}B^i_{n,|m|}B^j_{\nu,|\mu|}\Big(\sum_{l=j}^{j+i}C^{ab}_{i,l-j}T_l(\cos2\beta')+\sum_{l=l_0}^{j}C^{ab}_{i,j-l}T_l(\cos2\beta')+\sum_{l=1}^{i-j}C^{ab}_{i,l+j}T_l(\cos2\beta')\Big).$$
--
--   An empty range of summation contributes zero.
--
--   **Formalization Note** Stated as proved. For $k>k'$ the paper does not say what $a,b$ are, and it reuses the symbol $l_0=i-\min(i,j)$. The expansion holds with $a=(k'/k)^2$ and $b=1-(k'/k)^2$, which come from $\cos2\beta=1-a+a\cos2\beta'$, and with $l_0=j-\min(i,j)$. With $l_0=i-\min(i,j)$ the formula is false, for example for $i=2$, $j=0$. The expansions (B.3) enter as hypotheses, as in (3.49).
-- source:
--   Yuan, Wang, Zhang and Cai, Fast multipole method for Maxwell's equations in layered media, arXiv:2507.18491v1 (2025), claim c021; Section 3.4.3, eqs. (3.50)-(3.51), with eqs. (3.47)-(3.49), (A.1) and (B.3), PDF p. 19

import Mathlib
import Definitions.Def_Arxiv2507_18491_Basic

open MeasureTheory Filter Topology

namespace Arxiv2507_18491

theorem legendre_product_single_chebyshev (k k' : ℝ) (hk : 0 < k) (hk' : 0 < k')
    (krho : ℝ) (hkrho : 0 ≤ krho) (beta beta' : ℂ)
    (hsb : Complex.sin beta = (krho : ℂ) / k) (hcb : Complex.cos beta = vkz k krho / k)
    (hsb' : Complex.sin beta' = (krho : ℂ) / k') (hcb' : Complex.cos beta' = vkz k' krho / k')
    (n nu : ℕ) (m mu : ℤ) (hm : |m| ≤ n) (hmu : |mu| ≤ nu) (B1 B2 : ℕ → ℂ) (p1 p2 : ℂ)
    (hp1 : p1 = sgnPow m * tauLeg n m.natAbs beta *
      ∑ i ∈ Finset.range (Kn n m.natAbs + 1), B1 i * chebT i (Complex.cos (2 * beta)))
    (hp2 : p2 = sgnPow mu * tauLeg nu mu.natAbs beta' *
      ∑ j ∈ Finset.range (Kn nu mu.natAbs + 1), B2 j * chebT j (Complex.cos (2 * beta'))) :
    (k ≤ k' →
      p1 * p2 = sgnPow m * sgnPow mu / 2 * tauLeg n m.natAbs beta * tauLeg nu mu.natAbs beta' *
        ∑ i ∈ Finset.range (Kn n m.natAbs + 1), ∑ j ∈ Finset.range (Kn nu mu.natAbs + 1),
          B1 i * B2 j *
            ((∑ l ∈ Finset.Icc i (j + i),
                chebShiftCoeff (((k / k' : ℝ) : ℂ) ^ 2) (1 - ((k / k' : ℝ) : ℂ) ^ 2) j (l - i) *
                  chebT l (Complex.cos (2 * beta)))
              + (∑ l ∈ Finset.Icc (i - min i j) i,
                chebShiftCoeff (((k / k' : ℝ) : ℂ) ^ 2) (1 - ((k / k' : ℝ) : ℂ) ^ 2) j (i - l) *
                  chebT l (Complex.cos (2 * beta)))
              + (∑ l ∈ Finset.Icc 1 (j - i),
                chebShiftCoeff (((k / k' : ℝ) : ℂ) ^ 2) (1 - ((k / k' : ℝ) : ℂ) ^ 2) j (l + i) *
                  chebT l (Complex.cos (2 * beta))))) ∧
    (k' < k →
      p1 * p2 = sgnPow m * sgnPow mu / 2 * tauLeg n m.natAbs beta * tauLeg nu mu.natAbs beta' *
        ∑ i ∈ Finset.range (Kn n m.natAbs + 1), ∑ j ∈ Finset.range (Kn nu mu.natAbs + 1),
          B1 i * B2 j *
            ((∑ l ∈ Finset.Icc j (j + i),
                chebShiftCoeff (((k' / k : ℝ) : ℂ) ^ 2) (1 - ((k' / k : ℝ) : ℂ) ^ 2) i (l - j) *
                  chebT l (Complex.cos (2 * beta')))
              + (∑ l ∈ Finset.Icc (j - min i j) j,
                chebShiftCoeff (((k' / k : ℝ) : ℂ) ^ 2) (1 - ((k' / k : ℝ) : ℂ) ^ 2) i (j - l) *
                  chebT l (Complex.cos (2 * beta')))
              + (∑ l ∈ Finset.Icc 1 (i - j),
                chebShiftCoeff (((k' / k : ℝ) : ℂ) ^ 2) (1 - ((k' / k : ℝ) : ℂ) ^ 2) i (l + j) *
                  chebT l (Complex.cos (2 * beta'))))) := by sorry

end Arxiv2507_18491

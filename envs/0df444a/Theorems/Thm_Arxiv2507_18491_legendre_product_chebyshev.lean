-- Prove2me | Theorems.Thm_Arxiv2507_18491_legendre_product_chebyshev
-- name    : Arxiv2507_18491.legendre_product_chebyshev
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-26T13:04:47.675379+00:00
-- url     : https://prove2.me/theorems/f3a62ee7-a3c4-4d7b-845f-4aa6beec5079
-- title:
--   Eqs. (3.47)-(3.49): Chebyshev expansion of the product of associated Legendre functions for $k\le k'$
-- statement:
--   Let $0<k\le k'$, write $\gamma=k/k'\le1$, and let $k_\rho\ge0$. Let $\beta,\beta'\in\mathbb C$ satisfy $\sin\beta=k_\rho/k$, $\cos\beta=k_z/k$, $\sin\beta'=k_\rho/k'$ and $\cos\beta'=k'_z/k'$. Then:
--
--   1. $\cos2\beta=1-2k_\rho^2/k^2$, and $\cos2\beta'=1-2k_\rho^2/k'^2=1-\gamma^2+\gamma^2\cos2\beta$.
--   2. For every $j\ge0$, $T_j(\cos2\beta')=\sum_{s=0}^jC^{ab}_{js}T_s(\cos2\beta)$ with $a=\gamma^2$, $b=1-\gamma^2$ (eq. 3.48).
--   3. Let $|m|\le n$, $|\mu|\le\nu$, and suppose the Chebyshev expansions (B.3) hold at $\beta$ and $\beta'$:
--   $$\widehat P_n^m(\cos\beta)=\mathrm{sgn}(m)\tau_{n,|m|}(\beta)\sum_{i=0}^{K_n}B^i_{n,|m|}T_i(\cos2\beta),\qquad\widehat P_\nu^\mu(\cos\beta')=\mathrm{sgn}(\mu)\tau_{\nu,|\mu|}(\beta')\sum_{j=0}^{K_\nu}B^j_{\nu,|\mu|}T_j(\cos2\beta').$$
--   Then the product of these two values, $Q^{\nu\mu}_{nm}=\widehat P_n^m(\cos\beta)\widehat P_\nu^\mu(\cos\beta')$ (eq. 3.47), where $\widehat P_n^m(\cos\beta)$ and $\widehat P_\nu^\mu(\cos\beta')$ denote any two numbers satisfying the expansions above, equals
--   $$s_{m\mu}\tau_{n,|m|}(\beta)\tau_{\nu,|\mu|}(\beta')\sum_{i=0}^{K_n}\sum_{j=0}^{K_\nu}B^i_{n,|m|}B^j_{\nu,|\mu|}T_i(\cos2\beta)T_j(\cos2\beta')$$
--   $$=s_{m\mu}\tau_{n,|m|}(\beta)\tau_{\nu,|\mu|}(\beta')\sum_{i=0}^{K_n}\sum_{j=0}^{K_\nu}\sum_{l=0}^jB^i_{n,|m|}B^j_{\nu,|\mu|}C^{ab}_{jl}T_i(\cos2\beta)T_l(\cos2\beta),$$
--   where $s_{m\mu}=\mathrm{sgn}(m)\mathrm{sgn}(\mu)$ and $\mathrm{sgn}(x)=(-1)^{\min(0,x)}$ (eq. 3.49).
--
--   **Formalization Note** The printed $\cos\beta'=k_z'/k$ is read as $\cos\beta'=k_z'/k'$: the printed version contradicts $\sin\beta'=k_\rho/k'$ unless $k=k'$, and (3.47) uses $\widehat P_\nu^\mu(k_z'/k')=\widehat P_\nu^\mu(\cos\beta')$. The paper's recursion for the coefficients $B$ uses constants it does not define, so the expansions (B.3) at the two points enter as hypotheses, with the values $\widehat P$, $B$ arbitrary and $\tau_{nm}$, $K_n$ as defined in (B.1).
-- source:
--   Yuan, Wang, Zhang and Cai, Fast multipole method for Maxwell's equations in layered media, arXiv:2507.18491v1 (2025), claim c039; Section 3.4.3, the displays after (3.46), eqs. (3.47)-(3.49), with eqs. (A.1) and (B.3), PDF p. 19

import Mathlib
import Definitions.Def_Arxiv2507_18491_Basic

open MeasureTheory Filter Topology

namespace Arxiv2507_18491

theorem legendre_product_chebyshev (k k' : ℝ) (hk : 0 < k) (hk' : 0 < k') (hkk : k ≤ k')
    (krho : ℝ) (hkrho : 0 ≤ krho) (beta beta' : ℂ)
    (hsb : Complex.sin beta = (krho : ℂ) / k) (hcb : Complex.cos beta = vkz k krho / k)
    (hsb' : Complex.sin beta' = (krho : ℂ) / k') (hcb' : Complex.cos beta' = vkz k' krho / k') :
    Complex.cos (2 * beta) = 1 - 2 * (krho : ℂ) ^ 2 / (k : ℂ) ^ 2 ∧
    Complex.cos (2 * beta') = 1 - 2 * (krho : ℂ) ^ 2 / (k' : ℂ) ^ 2 ∧
    Complex.cos (2 * beta') =
      1 - ((k / k' : ℝ) : ℂ) ^ 2 + ((k / k' : ℝ) : ℂ) ^ 2 * Complex.cos (2 * beta) ∧
    (∀ j : ℕ, chebT j (Complex.cos (2 * beta')) =
      ∑ s ∈ Finset.range (j + 1),
        chebShiftCoeff (((k / k' : ℝ) : ℂ) ^ 2) (1 - ((k / k' : ℝ) : ℂ) ^ 2) j s *
          chebT s (Complex.cos (2 * beta))) ∧
    (∀ (n nu : ℕ) (m mu : ℤ), |m| ≤ n → |mu| ≤ nu → ∀ (B1 B2 : ℕ → ℂ) (p1 p2 : ℂ),
      p1 = sgnPow m * tauLeg n m.natAbs beta *
        ∑ i ∈ Finset.range (Kn n m.natAbs + 1), B1 i * chebT i (Complex.cos (2 * beta)) →
      p2 = sgnPow mu * tauLeg nu mu.natAbs beta' *
        ∑ j ∈ Finset.range (Kn nu mu.natAbs + 1), B2 j * chebT j (Complex.cos (2 * beta')) →
      p1 * p2 = sgnPow m * sgnPow mu * tauLeg n m.natAbs beta * tauLeg nu mu.natAbs beta' *
        ∑ i ∈ Finset.range (Kn n m.natAbs + 1), ∑ j ∈ Finset.range (Kn nu mu.natAbs + 1),
          B1 i * B2 j * chebT i (Complex.cos (2 * beta)) * chebT j (Complex.cos (2 * beta')) ∧
      p1 * p2 = sgnPow m * sgnPow mu * tauLeg n m.natAbs beta * tauLeg nu mu.natAbs beta' *
        ∑ i ∈ Finset.range (Kn n m.natAbs + 1), ∑ j ∈ Finset.range (Kn nu mu.natAbs + 1),
          ∑ l ∈ Finset.range (j + 1),
            B1 i * B2 j *
              chebShiftCoeff (((k / k' : ℝ) : ℂ) ^ 2) (1 - ((k / k' : ℝ) : ℂ) ^ 2) j l *
                chebT i (Complex.cos (2 * beta)) * chebT l (Complex.cos (2 * beta))) := by sorry

end Arxiv2507_18491

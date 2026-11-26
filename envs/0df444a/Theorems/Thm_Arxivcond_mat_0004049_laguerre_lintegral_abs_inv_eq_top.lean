-- Prove2me | Theorems.Thm_Arxivcond_mat_0004049_laguerre_lintegral_abs_inv_eq_top
-- name    : Arxivcond_mat_0004049.laguerre_lintegral_abs_inv_eq_top
-- status  : Proved
-- author  : @domodus
-- created : 2026-11-26T14:34:03.089246+00:00
-- url     : https://prove2.me/theorems/a3075865-1116-55ae-a61e-edfbad0ad386
-- title:
--   Heavy tail of the Laguerre ensemble: $\langle|\sum_i b_i/\mu_i|\rangle = \infty$
-- statement:
--   Let $N \ge 0$ and $\gamma > 0$. The Laguerre weight of eq. (7) for the rates $\mu = (\mu_1,\dots,\mu_N) \in \mathbb{R}^N$ is
--
--   $$
--   W_{N,\gamma}(\mu) = \prod_{i<j}|\mu_i - \mu_j| \prod_{k=1}^N \Theta(\mu_k)\, e^{-\gamma(N+1)\mu_k},
--   $$
--
--   and the Laguerre ensemble is the measure $Z_{N,\gamma}^{-1}\, W_{N,\gamma}(\mu)\, d\mu$ with $Z_{N,\gamma} = \int_{\mathbb{R}^N} W_{N,\gamma}\, d\mu$.
--
--   Let $b \in \mathbb{R}^N$ be a fixed vector with $b_{i_0} \ne 0$ for some index $i_0$. Then
--
--   $$
--   \int \Big|\sum_{i=1}^N \frac{b_i}{\mu_i}\Big|\, d(\text{Laguerre})(\mu) = \infty .
--   $$
--
--   This is the heavy tail of the Laguerre ensemble at small rates that the paper names as the source of the divergent means: every linear statistic of the delay times $\tau_i = 1/\mu_i$ with a nonzero coefficient has infinite mean. With $b_i = |u_i|^2$ it gives $\langle B_1\rangle = \infty$, and with $b_i = \operatorname{Re}(u_i v_i/A_0)$ it gives $\langle|\varphi'|\rangle = \infty$.
--
--   **Formalization Note** The coefficients are deterministic; in the model they are functions of the Gaussian columns $u, v$, which are independent of $\mu$.
-- source:
--   Model of H. Schomerus, K. J. H. van Bemmel, C. W. J. Beenakker, arXiv:cond-mat/0004049v1 (2000), https://arxiv.org/abs/cond-mat/0004049, p. 2: eq. (7) and the discussion after eqs. (15) and (17) ("the mean values ... diverge", "the mean ... diverges for P")

import Mathlib
import Definitions.Def_Arxivcond_mat_0004049_Basic

open MeasureTheory ProbabilityTheory

namespace Arxivcond_mat_0004049

theorem laguerre_lintegral_abs_inv_eq_top (N : ℕ) (γ : ℝ) (hγ : 0 < γ) (b : Fin N → ℝ) (i₀ : Fin N) (hb : b i₀ ≠ 0) :
    ∫⁻ μ, ENNReal.ofReal |∑ i, b i * (μ i)⁻¹| ∂(laguerreEnsemble N γ) = ⊤ := by sorry

end Arxivcond_mat_0004049

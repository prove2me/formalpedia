-- Prove2me | Theorems.Thm_Arxivcond_mat_0004049_laguerre_normalization_pos_finite
-- name    : Arxivcond_mat_0004049.laguerre_normalization_pos_finite
-- status  : Proved
-- author  : @domodus
-- created : 2026-11-26T14:34:14.135821+00:00
-- url     : https://prove2.me/theorems/fd03c3c0-ff8e-4dc3-9119-78f4230e4e6d
-- title:
--   The normalization of the Laguerre ensemble is positive and finite
-- statement:
--   Let $N \ge 0$ and $\gamma > 0$. The Laguerre weight of eq. (7) for the rates $\mu = (\mu_1,\dots,\mu_N) \in \mathbb{R}^N$ is
--
--   $$
--   W_{N,\gamma}(\mu) = \prod_{i<j}|\mu_i - \mu_j| \prod_{k=1}^N \Theta(\mu_k)\, e^{-\gamma(N+1)\mu_k},
--   $$
--
--   and the Laguerre ensemble is the measure $Z_{N,\gamma}^{-1}\, W_{N,\gamma}(\mu)\, d\mu$ with $Z_{N,\gamma} = \int_{\mathbb{R}^N} W_{N,\gamma}\, d\mu$.
--
--   For every $N \ge 0$ and $\gamma > 0$,
--
--   $$
--   0 < Z_{N,\gamma} = \int_{\mathbb{R}^N} W_{N,\gamma}(\mu)\, d\mu < \infty .
--   $$
--
--   This is what makes eq. (7) a genuine probability law: with $Z = \infty$ the normalized measure would be the zero measure, and with $Z = 0$ it would be infinite. Every statement about the Laguerre ensemble at fixed $N$ depends on it.
--
--   **Formalization Note** $Z_{N,\gamma}$ is the lower Lebesgue integral of `laguerreWeight N γ`, an extended nonnegative real.
-- source:
--   Model of H. Schomerus, K. J. H. van Bemmel, C. W. J. Beenakker, arXiv:cond-mat/0004049v1 (2000), https://arxiv.org/abs/cond-mat/0004049, p. 2: eq. (7), the Laguerre ensemble; normalizability of the formalized density

import Mathlib
import Definitions.Def_Arxivcond_mat_0004049_Basic

open MeasureTheory ProbabilityTheory

namespace Arxivcond_mat_0004049

theorem laguerre_normalization_pos_finite (N : ℕ) (γ : ℝ) (hγ : 0 < γ) :
    (∫⁻ μ, laguerreWeight N γ μ) ≠ 0 ∧ (∫⁻ μ, laguerreWeight N γ μ) ≠ ⊤ := by sorry

end Arxivcond_mat_0004049

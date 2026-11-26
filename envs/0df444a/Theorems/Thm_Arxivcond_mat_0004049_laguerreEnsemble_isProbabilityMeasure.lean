-- Prove2me | Theorems.Thm_Arxivcond_mat_0004049_laguerreEnsemble_isProbabilityMeasure
-- name    : Arxivcond_mat_0004049.laguerreEnsemble_isProbabilityMeasure
-- status  : Proved
-- author  : @domodus
-- created : 2026-11-26T14:34:09.046869+00:00
-- url     : https://prove2.me/theorems/6484bf83-b0f9-5a4e-9c23-72adc97b81d0
-- title:
--   The Laguerre ensemble of eq. (7) is a probability measure
-- statement:
--   Let $N \ge 0$ and $\gamma > 0$. The Laguerre weight of eq. (7) for the rates $\mu = (\mu_1,\dots,\mu_N) \in \mathbb{R}^N$ is
--
--   $$
--   W_{N,\gamma}(\mu) = \prod_{i<j}|\mu_i - \mu_j| \prod_{k=1}^N \Theta(\mu_k)\, e^{-\gamma(N+1)\mu_k},
--   $$
--
--   and the Laguerre ensemble is the measure $Z_{N,\gamma}^{-1}\, W_{N,\gamma}(\mu)\, d\mu$ with $Z_{N,\gamma} = \int_{\mathbb{R}^N} W_{N,\gamma}\, d\mu$.
--
--   For every $N \ge 0$ and $\gamma > 0$, the Laguerre ensemble is a probability measure on $\mathbb{R}^N$.
--
--   This lets later results use the ensemble as the law of the rates $\mu_i = 1/\tau_i$, for example to integrate constants or to apply results stated for probability measures.
-- source:
--   Model of H. Schomerus, K. J. H. van Bemmel, C. W. J. Beenakker, arXiv:cond-mat/0004049v1 (2000), https://arxiv.org/abs/cond-mat/0004049, p. 2: eq. (7), the Laguerre ensemble as the law of the rates

import Mathlib
import Definitions.Def_Arxivcond_mat_0004049_Basic

open MeasureTheory ProbabilityTheory

namespace Arxivcond_mat_0004049

theorem laguerreEnsemble_isProbabilityMeasure (N : ℕ) (γ : ℝ) (hγ : 0 < γ) :
    IsProbabilityMeasure (laguerreEnsemble N γ) := by sorry

end Arxivcond_mat_0004049

-- Prove2me | Theorems.Thm_Arxivcond_mat_0004049_laguerreWeight_measurable
-- name    : Arxivcond_mat_0004049.laguerreWeight_measurable
-- status  : Proved
-- author  : @domodus
-- created : 2026-11-26T14:34:05.476963+00:00
-- url     : https://prove2.me/theorems/e0803ec9-ecbc-4117-9bde-5917a1bcdfa7
-- title:
--   The Laguerre weight of eq. (7) is measurable
-- statement:
--   Let $N \ge 0$ and $\gamma > 0$. The Laguerre weight of eq. (7) for the rates $\mu = (\mu_1,\dots,\mu_N) \in \mathbb{R}^N$ is
--
--   $$
--   W_{N,\gamma}(\mu) = \prod_{i<j}|\mu_i - \mu_j| \prod_{k=1}^N \Theta(\mu_k)\, e^{-\gamma(N+1)\mu_k},
--   $$
--
--   and the Laguerre ensemble is the measure $Z_{N,\gamma}^{-1}\, W_{N,\gamma}(\mu)\, d\mu$ with $Z_{N,\gamma} = \int_{\mathbb{R}^N} W_{N,\gamma}\, d\mu$.
--
--   For every $N$ and every real $\gamma$, the weight $W_{N,\gamma} : \mathbb{R}^N \to [0,\infty]$ is Borel measurable.
--
--   This is the hypothesis needed to integrate against the Laguerre ensemble through its density, for example to rewrite $\int f\, d(\text{Laguerre}) = Z^{-1}\int W f\, d\mu$.
-- source:
--   Model of H. Schomerus, K. J. H. van Bemmel, C. W. J. Beenakker, arXiv:cond-mat/0004049v1 (2000), https://arxiv.org/abs/cond-mat/0004049, p. 2: eq. (7), the Laguerre ensemble; a well-posedness fact of the formalized model (definitions file Arxivcond_mat_0004049_Basic)

import Mathlib
import Definitions.Def_Arxivcond_mat_0004049_Basic

open MeasureTheory ProbabilityTheory

namespace Arxivcond_mat_0004049

theorem laguerreWeight_measurable (N : ℕ) (γ : ℝ) :
    Measurable (laguerreWeight N γ) := by sorry

end Arxivcond_mat_0004049

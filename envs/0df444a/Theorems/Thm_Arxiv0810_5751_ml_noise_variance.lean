-- Prove2me | Theorems.Thm_Arxiv0810_5751_ml_noise_variance
-- name    : Arxiv0810_5751.ml_noise_variance
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-24T06:43:22.674018+00:00
-- url     : https://prove2.me/theorems/302ea91e-2aab-4690-bead-8d7343779f6e
-- title:
--   Eq. (17): the maximum-likelihood noise variance
-- statement:
--   Let $\mathbf y\in\mathbb C^M$, let $\mathbf s_i:\mathbb C^P\to\mathbb C^M$, $i=1,\dots,K$, and let $\hat{\boldsymbol\theta}\in\mathbb C^P$ with nonzero residual $\mathbf r=\mathbf y-\sum_{i=1}^K\mathbf s_i(\hat{\boldsymbol\theta})$. For white noise $\mathbf\Pi=\sigma^2\mathbf I$, let
--
--   $$L(\hat{\boldsymbol\theta},\sigma^2)=\log\Big(\frac{1}{\pi^M|\sigma^2\mathbf I|}\exp\big(-\mathbf r^H(\sigma^2\mathbf I)^{-1}\mathbf r\big)\Big)=-M\log\pi-M\log\sigma^2-\frac{1}{\sigma^2}\mathbf r^H\mathbf r .$$
--
--   Then $\sigma^2\mapsto L(\hat{\boldsymbol\theta},\sigma^2)$ has exactly one maximiser over $\sigma^2>0$, namely
--
--   $$\widehat{\sigma^2}=\frac1M\Big(\mathbf y-\sum_{i=1}^K\mathbf s_i(\hat{\boldsymbol\theta})\Big)^H\Big(\mathbf y-\sum_{i=1}^K\mathbf s_i(\hat{\boldsymbol\theta})\Big).$$
--
--   **Formalization Note** The log-likelihood is defined as the logarithm of the density (15) at $\mathbf\Pi=\sigma^2\mathbf I$, not by the expanded formula (16). The hypothesis $\mathbf r\neq\mathbf 0$ is implicit in the paper: for $\mathbf r=\mathbf 0$ the likelihood is unbounded as $\sigma^2\to0$ and has no maximiser. The statement holds for every $\hat{\boldsymbol\theta}$, as in the paper's "given $\boldsymbol\theta$".
-- source:
--   Yatawatta, Zaroubi, de Bruyn, Koopmans and Noordam, Radio interferometric calibration using the SAGE algorithm, arXiv:0810.5751v1 (2008), claim c006; Section IV (Statistical Model Order Selection), eqs. (15)-(17), PDF p. 4

import Mathlib
import Definitions.Def_Arxiv0810_5751_Basic

open MeasureTheory Matrix
open scoped ComplexOrder

namespace Arxiv0810_5751

theorem ml_noise_variance {K M P : ℕ} (y : Fin M → ℂ) (s : Fin K → (Fin P → ℂ) → Fin M → ℂ)
    (θhat : Fin P → ℂ) (hr : residual y s θhat ≠ 0) :
    {σ2 : ℝ | 0 < σ2 ∧ ∀ τ : ℝ, 0 < τ → whiteLogLik τ y s θhat ≤ whiteLogLik σ2 y s θhat} =
      {mlNoiseVar y s θhat} := by sorry

end Arxiv0810_5751

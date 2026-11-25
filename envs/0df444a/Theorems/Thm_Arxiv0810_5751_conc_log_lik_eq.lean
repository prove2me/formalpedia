-- Prove2me | Theorems.Thm_Arxiv0810_5751_conc_log_lik_eq
-- name    : Arxiv0810_5751.conc_log_lik_eq
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-24T06:44:13.16219+00:00
-- url     : https://prove2.me/theorems/0df126b4-184f-4b9d-90a8-a169829c12d7
-- title:
--   Eq. (18): the log-likelihood at the maximum-likelihood noise variance
-- statement:
--   Let $\mathbf y\in\mathbb C^M$, let $\mathbf s_i:\mathbb C^P\to\mathbb C^M$, $i=1,\dots,K$, and let $\hat{\boldsymbol\theta}\in\mathbb C^P$ with nonzero residual $\mathbf r=\mathbf y-\sum_{i=1}^K\mathbf s_i(\hat{\boldsymbol\theta})$. Substituting the noise variance $\widehat{\sigma^2}=\frac1M\mathbf r^H\mathbf r$ of eq. (17) into the white-noise log-likelihood (16) gives
--
--   $$L(\hat{\boldsymbol\theta})=-M\log\pi-M-M\log\Big(\frac1M\Big(\mathbf y-\sum_{i=1}^K\mathbf s_i(\hat{\boldsymbol\theta})\Big)^H\Big(\mathbf y-\sum_{i=1}^K\mathbf s_i(\hat{\boldsymbol\theta})\Big)\Big).$$
--
--   This is the log-likelihood that enters Akaike's criterion (19).
--
--   **Formalization Note** As in eq. (17), the log-likelihood is the logarithm of the density (15) at $\mathbf\Pi=\widehat{\sigma^2}\mathbf I$. The hypothesis $\mathbf r\neq\mathbf 0$ is implicit in the paper (for $\mathbf r=\mathbf 0$ the right side contains $\log 0$).
-- source:
--   Yatawatta, Zaroubi, de Bruyn, Koopmans and Noordam, Radio interferometric calibration using the SAGE algorithm, arXiv:0810.5751v1 (2008), claim c007; Section IV (Statistical Model Order Selection), eqs. (16)-(18), PDF p. 4

import Mathlib
import Definitions.Def_Arxiv0810_5751_Basic

open MeasureTheory Matrix
open scoped ComplexOrder

namespace Arxiv0810_5751

theorem conc_log_lik_eq {K M P : ℕ} (y : Fin M → ℂ) (s : Fin K → (Fin P → ℂ) → Fin M → ℂ)
    (θhat : Fin P → ℂ) (hr : residual y s θhat ≠ 0) :
    whiteLogLik (mlNoiseVar y s θhat) y s θhat = concLogLik y s θhat := by sorry

end Arxiv0810_5751

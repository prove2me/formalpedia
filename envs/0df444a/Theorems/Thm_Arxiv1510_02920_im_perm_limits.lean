-- Prove2me | Theorems.Thm_Arxiv1510_02920_im_perm_limits
-- name    : Arxiv1510_02920.im_perm_limits
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T02:09:48.484428+00:00
-- url     : https://prove2.me/theorems/75301535-4b59-4fe6-8fe7-40f9ed867358
-- title:
--   Eqs. (6)-(7): the low- and high-frequency behaviour of $\mathrm{Im}\,\varepsilon$
-- statement:
--   Under the hypotheses of eq. (5), for every $x$,
--
--   $$\lim_{\omega\to0}\omega\,\operatorname{Im}\varepsilon(x,\omega)=-\frac{cf'(x)}{\gamma^2},\qquad\lim_{\omega\to\infty}\omega^3\operatorname{Im}\varepsilon(x,\omega)=4\gamma f(x)+cf'(x).$$
--
--   **Formalization Note** The paper writes $\operatorname{Im}\varepsilon\to-cf'/(\gamma^2\omega)$ and $\operatorname{Im}\varepsilon\to(4\gamma f+cf')/\omega^3$. These are stated as limits of $\omega\operatorname{Im}\varepsilon$ and $\omega^3\operatorname{Im}\varepsilon$, which remain meaningful when a coefficient vanishes. The limit at $0$ is two-sided over real $\omega\ne0$, as in the paper's "$\omega\to0$".
-- source:
--   T. G. Philbin, All-frequency reflectionlessness, arXiv:1510.02920v1 (2015), claim c004; unnumbered main text, eqs. (6) and (7), PDF p. 3

import Mathlib
import Definitions.Def_Arxiv1510_02920_Basic

open Filter Topology Asymptotics

namespace Arxiv1510_02920

theorem im_perm_limits (c : ℝ) (hc : 0 < c) (γ : ℝ) (hγ : 0 < γ)
    (f : ℝ → ℝ) (hf : Differentiable ℝ f) (x : ℝ) :
    Tendsto (fun ω : ℝ => ω * (perm c (ansatzP f γ) x (ω : ℂ)).im) (𝓝[≠] 0)
        (𝓝 (-c * deriv f x / γ ^ 2)) ∧
      Tendsto (fun ω : ℝ => ω ^ 3 * (perm c (ansatzP f γ) x (ω : ℂ)).im) atTop
        (𝓝 (4 * γ * f x + c * deriv f x)) := by sorry

end Arxiv1510_02920

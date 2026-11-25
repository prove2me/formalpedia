-- Prove2me | Theorems.Thm_Arxiv2111_09089_cayley_map_properties
-- name    : Arxiv2111_09089.cayley_map_properties
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T10:28:43.307038+00:00
-- url     : https://prove2.me/theorems/b2d3012d-69d7-4aaf-8b71-9e8faa8a1ba2
-- title:
--   Eq. (3): the Cayley transform maps the real axis onto the unit circle (as corrected)
-- statement:
--   Let $\alpha>0$, let $\xi(\mu)=(1+j\alpha)\mu$, and let $\mu(\eta)=-j\,(1+\eta)/(1-\eta)$ be the Cayley transform. Then:
--
--   1. $\mu(\eta)$ is real for every $\eta$ with $|\eta|=1$, $\eta\ne1$, and every real $\mu$ equals $\mu(\eta)$ for exactly one such $\eta$. So the real $\mu$ axis is mapped one-to-one onto the unit circle $C_1$ minus the point $\eta=1$.
--   2. $\mu(0)=-j$, and $\mu(\eta)\to j$ as $|\eta|\to\infty$ in any direction.
--   3. For $\eta\ne1$,
--   $$\frac{d\mu}{d\eta}=\frac{-2j}{(1-\eta)^2}.$$
--   4. If a spectral function $g$ is continuous at $\xi(-j)$ and at $\xi(j)$, then $g(\xi(\mu(\eta)))$ tends to the constant $g(\xi(-j))$ as $\eta\to0$ and to the constant $g(\xi(j))$ as $|\eta|\to\infty$ in any direction.
--
--   **Formalization Note** Eq. (3) prints $d\mu=-j\,d\eta/(1-\eta)^2$. The derivative of $-j(1+\eta)/(1-\eta)$ is $-2j/(1-\eta)^2$, so the printed formula lacks a factor $2$, and the corrected value is stated. The paper says that the constant limits of $g$ "can be easily shown". This holds when $g$ is finite and continuous at the two finite points $\xi(\mp j)$ to which $\eta\to0,\infty$ correspond, and that is the hypothesis used here.
-- source:
--   Y. Hadad, On the use of the Padé-Fourier approximation in fast evaluation of the Green's function of layered media, arXiv:2111.09089v1 (2021), claim c003; Section II-C, eqs. (2)-(3) and the text after eq. (4), Fig. 3, PDF p. 3

import Mathlib
import Definitions.Def_Arxiv2111_09089_Basic

open Complex MeasureTheory Filter Topology Asymptotics

namespace Arxiv2111_09089

theorem cayley_map_properties (α : ℝ) (hα : 0 < α) :
    (∀ η : ℂ, ‖η‖ = 1 → η ≠ 1 → (cayley η).im = 0) ∧
    (∀ μ : ℝ, ∃! η : ℂ, ‖η‖ = 1 ∧ η ≠ 1 ∧ cayley η = (μ : ℂ)) ∧
    cayley 0 = -I ∧
    Tendsto cayley (cocompact ℂ) (𝓝 I) ∧
    (∀ η : ℂ, η ≠ 1 → HasDerivAt cayley (-2 * I / (1 - η) ^ 2) η) ∧
    ∀ g : ℂ → ℂ, ContinuousAt g (xiOfMu α (-I)) → ContinuousAt g (xiOfMu α I) →
      Tendsto (fun η => g (xiOfMu α (cayley η))) (𝓝 0) (𝓝 (g (xiOfMu α (-I)))) ∧
      Tendsto (fun η => g (xiOfMu α (cayley η))) (cocompact ℂ) (𝓝 (g (xiOfMu α I))) := by sorry

end Arxiv2111_09089

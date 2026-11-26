-- Prove2me | Theorems.Thm_Arxiv2111_09089_pade_fourier_equal_orders
-- name    : Arxiv2111_09089.pade_fourier_equal_orders
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T10:39:11.542428+00:00
-- url     : https://prove2.me/theorems/f1bfaa8c-1274-41bc-9bfe-1d5e96240797
-- title:
--   Eq. (6): constant limits force $L=M$ in the Padé-Fourier approximation (as corrected)
-- statement:
--   Let $\alpha>0$, let $g$ be a spectral function, and let $\xi(\mu)=(1+j\alpha)\mu$. Consider a Padé-Fourier rational function
--
--   $$R(\eta)=\frac{P_L(\eta)}{Q_M(\eta)}=\frac{\sum_{l=-L}^{L}a_l\eta^l}{\sum_{m=-M}^{M}b_m\eta^m}$$
--
--   with $a_{\pm L}\ne0$ and $b_{\pm M}\ne0$. Suppose $R$ reproduces the constant limits of $g$ in the Cayley plane: $R(\eta)\to g(\xi(-j))$ as $\eta\to0$ and $R(\eta)\to g(\xi(j))$ as $|\eta|\to\infty$, with both constants nonzero. Then
--
--   $$L=M,\qquad\frac{a_{-M}}{b_{-M}}=g\big(\xi(\mu=-j)\big),\qquad\frac{a_M}{b_M}=g\big(\xi(\mu=j)\big).$$
--
--   This is the choice that lets the approximation capture the behaviour of $g$ at $\eta=0$ and $\eta=\infty$, which the paper calls global optimality.
--
--   **Formalization Note** The paper prints $a_{-N}/b_{-N}=g(\xi(\mu=j))$ and $a_N/b_N=g(\xi(\mu=-j))$. The index should be $M$ ($=L$), not the Laurent truncation order $N$. The two values are interchanged: $\eta\to0$ corresponds to $\mu=-j$ (eq. (3)), and $R(\eta)\to a_{-M}/b_{-M}$ there. The corrected assignment is stated. The paper's "necessarily $L=M$" needs the exact orders ($a_{\pm L},b_{\pm M}\ne0$) and nonzero limits, and both are hypotheses. With a limit $0$, $L<M$ is also possible.
-- source:
--   Y. Hadad, On the use of the Padé-Fourier approximation in fast evaluation of the Green's function of layered media, arXiv:2111.09089v1 (2021), claim c004; Section II-C, eq. (6) and the text after it, Fig. 3 caption, PDF pp. 3-4

import Mathlib
import Definitions.Def_Arxiv2111_09089_Basic

open Complex MeasureTheory Filter Topology Asymptotics

namespace Arxiv2111_09089

theorem pade_fourier_equal_orders (α : ℝ) (hα : 0 < α) (g : ℂ → ℂ) (a b : ℤ → ℂ) (L M : ℕ)
    (haL : a L ≠ 0) (haL' : a (-(L : ℤ)) ≠ 0) (hbM : b M ≠ 0) (hbM' : b (-(M : ℤ)) ≠ 0)
    (hg0 : g (xiOfMu α (-I)) ≠ 0) (hginf : g (xiOfMu α I) ≠ 0)
    (h0 : Tendsto (padeFourier a b L M) (𝓝[≠] 0) (𝓝 (g (xiOfMu α (-I)))))
    (hinf : Tendsto (padeFourier a b L M) (cocompact ℂ) (𝓝 (g (xiOfMu α I)))) :
    L = M ∧ a (-(M : ℤ)) / b (-(M : ℤ)) = g (xiOfMu α (-I)) ∧
      a M / b M = g (xiOfMu α I) := by sorry

end Arxiv2111_09089

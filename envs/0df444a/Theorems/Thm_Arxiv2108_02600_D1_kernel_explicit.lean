-- Prove2me | Theorems.Thm_Arxiv2108_02600_D1_kernel_explicit
-- name    : Arxiv2108_02600.D1_kernel_explicit
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T09:48:22.091794+00:00
-- url     : https://prove2.me/theorems/7275cfca-3e45-518f-bef2-27fb656f2370
-- title:
--   Section 3.2: explicit form of the $D_1$ kernel $A^{(2)}$
-- statement:
--   Let $f\in B^{(n)}_{c,M}$, $s\ne t$, $r=r(s,t)$, and let $A^{(2)}_{jk}(s,t)=2[P^{(y)}(G_{j\cdot}(x,y))^\top]_k\sqrt{1+f'(t)^2}$ at $x=x(s)$, $y=y(t)$ be the kernel of $D_1$, where the stress operator acts in $y$ with the upward normal $\nu(t)$ and $\tilde\mu,\tilde\lambda$ are given by (2.10). Write $h_1=\kappa_sH^{(1)}_1(\kappa_sr)/r$, $h_2=\kappa_s^2H^{(1)}_2(\kappa_sr)-\kappa_p^2H^{(1)}_2(\kappa_pr)$ and $h_3=\kappa_s^3H^{(1)}_3(\kappa_sr)-\kappa_p^3H^{(1)}_3(\kappa_pr)$. Then
--
--   $$\begin{aligned}A^{(2)}_{jk}={}&(\mu+\tilde\mu)\Big\{\Big[-\frac{i}{2\mu}h_1+\frac{i}{2\omega^2}\frac{h_2}{r^2}\Big]\delta_{jk}-\frac{i}{2\omega^2}\frac{h_3}{r^3}(x_j-y_j)(x_k-y_k)\Big\}\big[(s-t)f'(t)+f(t)-f(s)\big]\\&-(\mu+\tilde\mu)\frac{i}{2\omega^2}\frac{h_2}{r^2}\big[(x_j-y_j)l_k(t)+(x_k-y_k)l_j(t)\big]\\&+\tilde\lambda\Big[\frac{i}{2\mu}h_1-\frac{2i}{\omega^2}\frac{h_2}{r^2}+\frac{i}{2\omega^2}\frac{h_3}{r}\Big](x_j-y_j)l_k(t)-\tilde\mu\frac{i}{2\mu}h_1\big[(f(s)-f(t))\delta_{j1}-(s-t)\delta_{j2}\big]l^\perp_k(t),\end{aligned}$$
--
--   with $x_j-y_j=x_j(s)-y_j(t)$, $l(t)=(-f'(t),1)$ and $l^\perp(t)=(1,f'(t))$.
-- source:
--   J. Li, X. Liu, B. Zhang and H. Zhang, The Nyström method for elastic wave scattering by unbounded rough surfaces, arXiv:2108.02600v1 (2021), claim c004; Section 3.2, unnumbered display before (3.16), PDF p. 10

import Mathlib
import Definitions.Def_Arxiv2108_02600_Basic

open MeasureTheory Filter Topology

namespace Arxiv2108_02600

theorem D1_kernel_explicit (P : Lame) (n : ℕ) (c M : ℝ) (hM : 0 < M) (f : ℝ → ℝ)
    (hf : InB n c M f) (s t : ℝ) (hst : s ≠ t) (j k : Fin 2) :
    let r : ℝ := rdist f s t
    let rc : ℂ := (r : ℂ)
    let I := Complex.I
    let mu : ℂ := (P.mu : ℂ)
    let om2 : ℂ := (P.omega : ℂ) ^ 2
    let h1 : ℂ := (P.ks : ℂ) * hankel1 1 (P.ks * r) / rc
    let h2 : ℂ := (P.ks : ℂ) ^ 2 * hankel1 2 (P.ks * r) - (P.kp : ℂ) ^ 2 * hankel1 2 (P.kp * r)
    let h3 : ℂ := (P.ks : ℂ) ^ 3 * hankel1 3 (P.ks * r) - (P.kp : ℂ) ^ 3 * hankel1 3 (P.kp * r)
    let d := dvec f s t
    kerA2 P f s t j k =
      ((P.mu + P.muT : ℝ) : ℂ) *
          (((if j = k then (1 : ℂ) else 0) * (-(I / (2 * mu)) * h1 + I / (2 * om2) * h2 / rc ^ 2) -
              I / (2 * om2) * h3 / rc ^ 3 * ((d j * d k : ℝ) : ℂ)) *
            (((s - t) * deriv f t + f t - f s : ℝ) : ℂ))
        - ((P.mu + P.muT : ℝ) : ℂ) * (I / (2 * om2)) * h2 / rc ^ 2 *
            ((d j * lvec f t k + d k * lvec f t j : ℝ) : ℂ)
        + (P.lamT : ℂ) * (I / (2 * mu) * h1 - 2 * I / om2 * h2 / rc ^ 2 + I / (2 * om2) * h3 / rc) *
            ((d j * lvec f t k : ℝ) : ℂ)
        - (P.muT : ℂ) * (I / (2 * mu)) * h1 *
            ((((f s - f t) * (if j = 0 then 1 else 0) - (s - t) * (if j = 1 then 1 else 0)) *
              lperp f t k : ℝ) : ℂ) := by sorry

end Arxiv2108_02600

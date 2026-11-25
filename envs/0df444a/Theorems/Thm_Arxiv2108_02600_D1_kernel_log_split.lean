-- Prove2me | Theorems.Thm_Arxiv2108_02600_D1_kernel_log_split
-- name    : Arxiv2108_02600.D1_kernel_log_split
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T09:52:50.545379+00:00
-- url     : https://prove2.me/theorems/421f600c-e139-5b30-8558-17926ba5ba8a
-- title:
--   Eqs. (3.16)–(3.17): splitting off the logarithmic part of the $D_1$ kernel
-- statement:
--   Let $f\in B^{(n)}_{c,M}$ ($M>0$), let $A^{(2)}$ be the kernel of $D_1$ and let $B^{(2)}$ be given by (3.16). This is the expression obtained from $A^{(2)}$ by replacing each $iH^{(1)}_m(\kappa r)$ by $-\frac2\pi J_m(\kappa r)$:
--
--   $$\begin{aligned}B^{(2)}_{jk}={}&(\mu+\tilde\mu)\Big\{\Big[\frac{1}{\pi\mu}\frac{\kappa_sJ_1(\kappa_sr)}{r}-\frac{1}{\pi\omega^2}\frac{j_2}{r^2}\Big]\delta_{jk}+\frac{1}{\pi\omega^2}\frac{j_3}{r^3}(x_j-y_j)(x_k-y_k)\Big\}\big[(s-t)f'(t)+f(t)-f(s)\big]\\&+(\mu+\tilde\mu)\frac{1}{\pi\omega^2}\frac{j_2}{r^2}\big[(x_j-y_j)l_k+(x_k-y_k)l_j\big]+\tilde\lambda\Big[-\frac{1}{\pi\mu}\frac{\kappa_sJ_1(\kappa_sr)}{r}+\frac{4}{\pi\omega^2}\frac{j_2}{r^2}-\frac{1}{\pi\omega^2}\frac{j_3}{r}\Big](x_j-y_j)l_k\\&+\tilde\mu\frac{1}{\pi\mu}\frac{\kappa_sJ_1(\kappa_sr)}{r}\big[(f(s)-f(t))\delta_{j1}-(s-t)\delta_{j2}\big]l^\perp_k,\end{aligned}$$
--
--   with $j_2=\kappa_s^2J_2(\kappa_sr)-\kappa_p^2J_2(\kappa_pr)$ and $j_3=\kappa_s^3J_3(\kappa_sr)-\kappa_p^3J_3(\kappa_pr)$. Let $C^{(2)}=A^{(2)}-B^{(2)}\ln|s-t|$ (3.17). Then $A^{(2)}=B^{(2)}\ln|s-t|+C^{(2)}$ for $s\ne t$, and each entry $C^{(2)}_{jk}$ extends to a continuous function on $\mathbb R^2$.
--
--   **Formalization Note** The paper leaves implicit that $C^{(2)}$ has no logarithmic singularity. It is stated here as continuous extendability across the diagonal. Since $C^{(2)}$ is defined by (3.17), the identity $A^{(2)}=B^{(2)}\ln|s-t|+C^{(2)}$ holds by definition; the content of the statement is the continuous extension. The diagonal values (3.18)–(3.19) are not part of this statement.
-- source:
--   J. Li, X. Liu, B. Zhang and H. Zhang, The Nyström method for elastic wave scattering by unbounded rough surfaces, arXiv:2108.02600v1 (2021), claim c005; Section 3.2, eqs. (3.16)-(3.17), PDF pp. 10-11

import Mathlib
import Definitions.Def_Arxiv2108_02600_Basic

open MeasureTheory Filter Topology

namespace Arxiv2108_02600

theorem D1_kernel_log_split (P : Lame) (n : ℕ) (c M : ℝ) (hM : 0 < M) (f : ℝ → ℝ)
    (hf : InB n c M f) (j k : Fin 2) :
    (∀ s t : ℝ, s ≠ t →
      kerA2 P f s t j k = kerB2 P f s t j k * (Real.log |s - t| : ℂ) + kerC2 P f s t j k) ∧
    ∃ F : ℝ × ℝ → ℂ, Continuous F ∧ ∀ s t : ℝ, s ≠ t → F (s, t) = kerC2 P f s t j k := by sorry

end Arxiv2108_02600

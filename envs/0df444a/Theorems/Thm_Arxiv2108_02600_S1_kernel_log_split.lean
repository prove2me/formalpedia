-- Prove2me | Theorems.Thm_Arxiv2108_02600_S1_kernel_log_split
-- name    : Arxiv2108_02600.S1_kernel_log_split
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T09:43:40.315946+00:00
-- url     : https://prove2.me/theorems/7f60d6a5-53fb-4a90-b012-98f7aad5fd31
-- title:
--   Eqs. (3.8)–(3.9): splitting off the logarithmic part of the $S_1$ kernel
-- statement:
--   Let $f\in B^{(n)}_{c,M}$ ($M>0$) describe the surface $\Gamma$, and let $A^{(1)}(s,t)=2G(x(s),y(t))\sqrt{1+f'(t)^2}$ be the kernel of $S_1$. Let $B^{(1)}$ be given by (3.8):
--
--   $$B^{(1)}_{jk}=\frac1\pi\Big\{\Big[-\frac1\mu J_0(\kappa_sr)+\frac{1}{\omega^2}\frac{\kappa_sJ_1(\kappa_sr)-\kappa_pJ_1(\kappa_pr)}{r}\Big]\delta_{jk}-\frac1{\omega^2}\frac{\kappa_s^2J_2(\kappa_sr)-\kappa_p^2J_2(\kappa_pr)}{r^2}(x_j(s)-y_j(t))(x_k(s)-y_k(t))\Big\}\sqrt{1+f'(t)^2},$$
--
--   and let $C^{(1)}=A^{(1)}-B^{(1)}\ln|s-t|$ (3.9). Then $A^{(1)}=B^{(1)}\ln|s-t|+C^{(1)}$ for $s\ne t$, and $B^{(1)}$ carries the whole logarithmic singularity: each entry $C^{(1)}_{jk}$, defined for $s\ne t$, extends to a continuous function on $\mathbb R^2$.
--
--   **Formalization Note** The paper leaves implicit that $C^{(1)}$ has no logarithmic singularity. It is stated here as continuous extendability across the diagonal. Since $C^{(1)}$ is defined by (3.9), the identity $A^{(1)}=B^{(1)}\ln|s-t|+C^{(1)}$ holds by definition; the content of the statement is the continuous extension. The diagonal values (3.15) are not part of this statement.
-- source:
--   J. Li, X. Liu, B. Zhang and H. Zhang, The Nyström method for elastic wave scattering by unbounded rough surfaces, arXiv:2108.02600v1 (2021), claim c002; Section 3.1, eqs. (3.8)-(3.9), PDF p. 9

import Mathlib
import Definitions.Def_Arxiv2108_02600_Basic

open MeasureTheory Filter Topology

namespace Arxiv2108_02600

theorem S1_kernel_log_split (P : Lame) (n : ℕ) (c M : ℝ) (hM : 0 < M) (f : ℝ → ℝ)
    (hf : InB n c M f) (j k : Fin 2) :
    (∀ s t : ℝ, s ≠ t →
      kerA1 P f s t j k = kerB1 P f s t j k * (Real.log |s - t| : ℂ) + kerC1 P f s t j k) ∧
    ∃ F : ℝ × ℝ → ℂ, Continuous F ∧ ∀ s t : ℝ, s ≠ t → F (s, t) = kerC1 P f s t j k := by sorry

end Arxiv2108_02600

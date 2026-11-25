-- Prove2me | Theorems.Thm_Arxiv2210_02565_grad_green_difference_expansion
-- name    : Arxiv2210_02565.grad_green_difference_expansion
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T12:58:19.7308+00:00
-- url     : https://prove2.me/theorems/c6ebc38b-7193-4b8a-9882-346e24e684d0
-- title:
--   Sec. VI: expansion of $\nabla[G_2-G_1]$ as $|r-r'|\to0$ (as proved: coefficient $(k_2^2-k_1^2)/(8\pi)$)
-- statement:
--   Let $k_1,k_2\in\mathbb C$ and $G_j(\mathbf r,\mathbf r')=e^{ik_j|\mathbf r-\mathbf r'|}/(4\pi|\mathbf r-\mathbf r'|)$ (eq. 9), and let $\nabla$ act on $\mathbf r$. Then, as $\mathbf r\to\mathbf r'$ with $\mathbf r\ne\mathbf r'$,
--
--   $$\nabla\big[G_2(\mathbf r,\mathbf r')-G_1(\mathbf r,\mathbf r')\big]=-\frac{k_2^2-k_1^2}{8\pi}\,\frac{\mathbf r-\mathbf r'}{|\mathbf r-\mathbf r'|}+o(1).$$
--
--   In particular, for every $R>0$ there is a constant $C$ such that $\big|\nabla[G_2(\mathbf r,\mathbf r')-G_1(\mathbf r,\mathbf r')]\big|\le C$ whenever $0<|\mathbf r-\mathbf r'|\le R$. So the kernel of the integrals $I^{(3)}_{m,n}$ in the off-diagonal blocks of the MoM matrix stays bounded.
--
--   **Formalization Note** The paper prints the coefficient as $(k_2^2-k_1^2)/2$. With $G_j$ as defined in eq. (9), the expansion $G_2-G_1=\frac{i(k_2-k_1)}{4\pi}-\frac{(k_2^2-k_1^2)}{8\pi}|\mathbf r-\mathbf r'|+O(|\mathbf r-\mathbf r'|^2)$ gives the coefficient $(k_2^2-k_1^2)/(8\pi)$, which is stated here. The printed value would hold for $G$ without the factor $1/(4\pi)$. The boundedness conclusion is unaffected. The boundedness is stated for the factor $\nabla[G_2-G_1]$, uniformly in $\mathbf r'$ for $|\mathbf r-\mathbf r'|$ bounded, as needed on the bounded surface $\Gamma_A$.
-- source:
--   Arrieta and Pérez-Arancibia, Windowed Green Function MoM for Second-Kind Surface Integral Equation Formulations of Layered Media Electromagnetic Scattering Problems, arXiv:2210.02565v1 (2022), claim c007; Section VI (MoM discretization), display after the integrals I^(1)-I^(3), with eq. (9), PDF p. 5

import Mathlib
import Definitions.Def_Arxiv2210_02565_Basic

open Filter Topology

namespace Arxiv2210_02565

theorem grad_green_difference_expansion (k1 k2 : ℂ) :
    (∀ r' : Space,
      Tendsto (fun r : Space => grad (fun x => greenFn k2 x r' - greenFn k1 x r') r +
          ((k2 ^ 2 - k1 ^ 2) / (8 * Real.pi)) • toC (‖r - r'‖⁻¹ • (r - r')))
        (𝓝[≠] r') (𝓝 0)) ∧
    ∀ R : ℝ, 0 < R → ∃ C : ℝ, ∀ x y : Space, 0 < ‖x - y‖ → ‖x - y‖ ≤ R →
      ‖grad (fun q => greenFn k2 q y - greenFn k1 q y) x‖ ≤ C := by sorry

end Arxiv2210_02565

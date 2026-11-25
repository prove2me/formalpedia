-- Prove2me | Theorems.Thm_Arxiv1901_08703_np_well_posed
-- name    : Arxiv1901_08703.np_well_posed
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T05:50:49.606016+00:00
-- url     : https://prove2.me/theorems/5a8ff25c-fb8f-41b6-8e01-97057025eca7
-- title:
--   Theorem 2.7: well-posedness of the Neumann problem (NP)
-- statement:
--   Let $h\in C^2(\mathbb R)$ have compact support and $k>0$. For every incident direction $d\in\mathbb S^1_-$ the Neumann problem (NP) with data $f=-(\partial u^i/\partial\nu+\partial u^r/\partial\nu)$ has a solution $u^s\in H^1_{loc}(D_+)$, and any two solutions coincide in $D_+$. Moreover, for every $\rho>0$ there is a constant $C$ such that for every $d\in\mathbb S^1_-$ and the solution $u^s=u^s(\cdot;d)$,
--   $$\|u^s\|_{H^1(D^+_\rho)}\le C\left\|\frac{\partial u^i}{\partial\nu}+\frac{\partial u^r}{\partial\nu}\right\|_{L^2(\Gamma)},\qquad D^+_\rho=B_\rho\cap D_+.\tag{2.32}$$
--
--   **Formalization Note** The paper writes $R$ for the radius in (2.32), the same letter as the radius of the disc that contains the perturbation; it is written $\rho$ here. The paper does not say what $C$ depends on. The statement takes $C$ depending on $\rho$ (and on $h$, $k$) but not on $d$. $\|u\|_{H^1(D)}^2=\int_D(|u|^2+|\nabla u|^2)\,dx$.
-- source:
--   Qu, Zhang and Zhang, A novel integral equation for scattering by locally rough surfaces and application to the inverse problem: the Neumann case, arXiv:1901.08703v1 (2019), claim c007; Section 2, Theorem 2.7, eq. (2.32), PDF p. 13

import Mathlib
import Definitions.Def_Arxiv1901_08703_Basic

open MeasureTheory

namespace Arxiv1901_08703

theorem np_well_posed (k : ℝ) (hk : 0 < k) (h : ℝ → ℝ) (hh : IsLocalProfile h) :
    (∀ d : R2, IsLowerDir d →
      (∃ u : R2 → ℂ, IsNPSolution k h (incData k d h) u) ∧
      ∀ u v : R2 → ℂ, IsNPSolution k h (incData k d h) u →
        IsNPSolution k h (incData k d h) v → ∀ x ∈ Dplus h, u x = v x) ∧
    ∀ ρ : ℝ, 0 < ρ → ∃ C : ℝ, ∀ d : R2, IsLowerDir d → ∀ u : R2 → ℂ,
      IsNPSolution k h (incData k d h) u →
        h1Norm (Dplus h ∩ Metric.ball 0 ρ) u ≤ C * l2Gam h (incData k d h) := by sorry

end Arxiv1901_08703

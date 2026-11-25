-- Prove2me | Theorems.Thm_Arxiv1901_08703_corner_split_star_part_norm_lt_one
-- name    : Arxiv1901_08703.corner_split_star_part_norm_lt_one
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T05:44:22.79891+00:00
-- url     : https://prove2.me/theorems/6836e332-a3d6-4357-bad4-b19f84aaeb0d
-- title:
--   Section 3.1, eq. (3.1): the corner part $\hat A^\star_{11}$ has norm $<1$ and $\hat A^\circ_{11}$ is compact
-- statement:
--   Let $h\in C^2(\mathbb R)$ have compact support, $k>0$, and let $R>0$ be such that $\Gamma_p\subset B_R$. Let $\hat A_{11}=B$ be the upper-left $2\times2$ block of $A$, acting on $L^2(\Gamma_R)\times L^2(\partial B_R^-)$. For $r>0$, split its kernel as $\hat A_{11}(x,y)=\hat A^\star_{11}(x,y)+\hat A^\circ_{11}(x,y)$ (eq. (3.1)), where $\hat A^\star_{11}(x,y)=\hat A_{11}(x,y)$ if $x$ and $y$ both lie within distance $r$ of the same corner ($x_A$ or $x_B$) of $\partial D_R^-$, and $\hat A^\star_{11}(x,y)=0$ otherwise. Then there is $r_0>0$ such that for every $0<r<r_0$:
--
--   1. $\hat A^\star_{11}$ is a bounded operator on $L^2(\Gamma_R)\times L^2(\partial B_R^-)$ with $\|\hat A^\star_{11}\|<1$, so that $(I+\hat A^\star_{11})^{-1}$ exists;
--   2. $\hat A^\circ_{11}=\hat A_{11}-\hat A^\star_{11}$ is a compact operator on that space.
--
--   **Formalization Note** The paper only says that $x$ and $y$ are "close enough" to the same corner. Here this is read as distance less than $r$ from that corner, for every sufficiently small $r$, as in Step I.2 of the proof of Theorem 2.4. The norm is the operator norm for the maximum of the two $L^2$ norms.
-- source:
--   Qu, Zhang and Zhang, A novel integral equation for scattering by locally rough surfaces and application to the inverse problem: the Neumann case, arXiv:1901.08703v1 (2019), claim c010; Section 3.1, eq. (3.1) and the text after it, PDF p. 15

import Mathlib
import Definitions.Def_Arxiv1901_08703_Basic

open MeasureTheory

namespace Arxiv1901_08703

theorem corner_split_star_part_norm_lt_one (k : ℝ) (hk : 0 < k) (h : ℝ → ℝ)
    (hh : IsLocalProfile h) (R : ℝ) (hR : PerturbationInBall h R) :
    ∃ r0 : ℝ, 0 < r0 ∧ ∀ r : ℝ, 0 < r → r < r0 →
      (∃ T : Ysp h R →L[ℂ] Ysp h R, ‖T‖ < 1 ∧ ∀ psi : Ysp h R,
        ⇑(T psi).1 =ᵐ[muG h R] opBstar1 k h R r ⇑psi.1 ⇑psi.2 ∧
        ⇑(T psi).2 =ᵐ[muB R] opBstar2 k h R r ⇑psi.1 ⇑psi.2) ∧
      (∃ T' : Ysp h R →L[ℂ] Ysp h R, IsCompactOperator T' ∧ ∀ psi : Ysp h R,
        ⇑(T' psi).1 =ᵐ[muG h R]
          (fun t => opB1 k h R ⇑psi.1 ⇑psi.2 t - opBstar1 k h R r ⇑psi.1 ⇑psi.2 t) ∧
        ⇑(T' psi).2 =ᵐ[muB R]
          (fun θ => opB2 k h R ⇑psi.1 ⇑psi.2 θ - opBstar2 k h R r ⇑psi.1 ⇑psi.2 θ)) := by sorry

end Arxiv1901_08703

-- Prove2me | Theorems.Thm_DimensionalCollapse_strong_augmentation_vanishing_singular_values
-- name    : DimensionalCollapse.strong_augmentation_vanishing_singular_values
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T06:53:42.658606+00:00
-- url     : https://prove2.me/theorems/dfe1e394-fbf1-40f5-ba71-d577c6d110fe
-- title:
--   Theorem 1: with fixed $X$ having a negative eigenvalue, $W$ has vanishing singular values
-- statement:
--   Let $X\in\mathbb{R}^{n\times n}$ be a fixed symmetric matrix with a negative eigenvalue, and let $W:[0,\infty)\to\mathbb{R}^{d\times n}$ be differentiable with
--   $$\dot W(t)=W(t)\,X\qquad(t\ge0).$$
--   Then $W$ has vanishing singular values: the smallest singular value of $W(t)$ tends to $0$,
--   $$\sigma_{\min}\big(W(t)\big)\longrightarrow0\qquad(t\to\infty).$$
--
--   This is the strong-augmentation mechanism of dimensional collapse: by Lemma 1 and eq. (5) the linear model evolves by $\dot W=WX$, and by Lemma 2 $X$ has a negative eigenvalue when the augmentation covariance dominates the data covariance in some direction.
--
--   **Formalization Note** "Fixed matrix $X$" is encoded as a constant symmetric matrix (the matrix of eq. (6) is symmetric by Lemma 2). The flow is required on $[0,\infty)$ with a one-sided derivative at $t=0$. $\sigma_{\min}$ is the smallest of the $n$ singular values; it is $0$ when $d<n$, so for $d<n$ the statement holds trivially and its content is the case $n\le d$. For $d<n$ the paper's claim, read with the usual $\min(d,n)$ singular values, is false: $d=1$, $n=2$, $X=\mathrm{diag}(1,-1)$, $W(0)=(1,0)$ gives $W(t)=(e^t,0)$, whose only singular value is $e^t$. The paper's "$W(\infty)$ is rank deficient" is stated as this limit, since $W(t)$ need not converge.
-- source:
--   Jing, Vincent, LeCun and Tian, Understanding Dimensional Collapse in Contrastive Self-supervised Learning, ICLR 2022, arXiv:2110.09348v3, Section 4.2, Theorem 1, p. 4; proof in Appendix B.3, p. 14

import Mathlib
import Definitions.Def_DimensionalCollapse_Basic

open Matrix Filter Topology

namespace DimensionalCollapse

theorem strong_augmentation_vanishing_singular_values {n d : ℕ}
    (X : Matrix (Fin n) (Fin n) ℝ) (hX : X.IsSymm)
    (hneg : ∃ μ : ℝ, μ < 0 ∧ ∃ v : Fin n → ℝ, v ≠ 0 ∧ X *ᵥ v = μ • v)
    (W : ℝ → Matrix (Fin d) (Fin n) ℝ)
    (hW : ∀ t, 0 ≤ t → ∀ a b,
      HasDerivWithinAt (fun s => W s a b) ((W t * X) a b) (Set.Ici 0) t) :
    Tendsto (fun t => minSingVal (W t)) atTop (𝓝 0) := by sorry

end DimensionalCollapse

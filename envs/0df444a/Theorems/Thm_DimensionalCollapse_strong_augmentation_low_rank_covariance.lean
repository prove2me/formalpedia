-- Prove2me | Theorems.Thm_DimensionalCollapse_strong_augmentation_low_rank_covariance
-- name    : DimensionalCollapse.strong_augmentation_low_rank_covariance
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T06:54:11.70946+00:00
-- url     : https://prove2.me/theorems/11175d94-9de3-458f-8b77-f80215a091e1
-- title:
--   Corollary 1 (as proved): dimensional collapse caused by strong augmentation
-- statement:
--   Let $N\ge1$ and $n\le d$. Let $x_1,\dots,x_N\in\mathbb{R}^n$, let $X\in\mathbb{R}^{n\times n}$ be a fixed symmetric matrix with a negative eigenvalue, and let $W:[0,\infty)\to\mathbb{R}^{d\times n}$ be differentiable with $\dot W(t)=W(t)X$ for $t\ge0$. Let
--   $$C(t)=\frac1N\sum_{i=1}^N\big(z_i(t)-\bar z(t)\big)\big(z_i(t)-\bar z(t)\big)^\top,\qquad z_i(t)=W(t)x_i,\quad \bar z(t)=\frac1N\sum_i z_i(t),$$
--   be the covariance matrix of the embeddings. Then $C(t)$ becomes low-rank: its smallest singular value tends to zero,
--   $$\sigma_{\min}\big(C(t)\big)\longrightarrow0\qquad(t\to\infty).$$
--
--   This is the paper's dimensional collapse in embedding space caused by strong augmentation.
--
--   **Formalization Note** The paper states the corollary without dimensions. The hypothesis $n\le d$ is added because the conclusion fails for $d<n$: with $d=1$, $n=2$, $X=\mathrm{diag}(-1,1)$, $W(0)=(1,1)$ and data $\pm e_1,\pm e_2$, one gets $C(t)=(e^{-2t}+e^{2t})/2\to\infty$. For $n<d$ the conclusion holds trivially, since $C(t)$ has rank at most $n<d$; the non-trivial case is $n=d$. The hypothesis $N\ge1$ is the paper's setting of a sample covariance; the statement would also hold for $N=0$, where $C=0$. "Becomes low-rank" is stated as the smallest singular value of $C(t)$ tending to $0$, the sense of the paper's argument.
-- source:
--   Jing, Vincent, LeCun and Tian, Understanding Dimensional Collapse in Contrastive Self-supervised Learning, ICLR 2022, arXiv:2110.09348v3, Section 4.2, Corollary 1 and the paragraph after it, p. 4

import Mathlib
import Definitions.Def_DimensionalCollapse_Basic

open Matrix Filter Topology

namespace DimensionalCollapse

theorem strong_augmentation_low_rank_covariance {N n d : ℕ} (hN : 0 < N) (hnd : n ≤ d)
    (x : Fin N → Fin n → ℝ)
    (X : Matrix (Fin n) (Fin n) ℝ) (hX : X.IsSymm)
    (hneg : ∃ μ : ℝ, μ < 0 ∧ ∃ v : Fin n → ℝ, v ≠ 0 ∧ X *ᵥ v = μ • v)
    (W : ℝ → Matrix (Fin d) (Fin n) ℝ)
    (hW : ∀ t, 0 ≤ t → ∀ a b,
      HasDerivWithinAt (fun s => W s a b) ((W t * X) a b) (Set.Ici 0) t) :
    Tendsto (fun t => minSingVal (embCov x (W t))) atTop (𝓝 0) := by sorry

end DimensionalCollapse

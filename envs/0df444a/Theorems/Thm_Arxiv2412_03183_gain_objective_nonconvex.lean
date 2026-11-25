-- Prove2me | Theorems.Thm_Arxiv2412_03183_gain_objective_nonconvex
-- name    : Arxiv2412_03183.gain_objective_nonconvex
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T13:47:48.983824+00:00
-- url     : https://prove2.me/theorems/16d0e97b-da55-48ed-8fbe-3d4593164c89
-- title:
--   Eq. (12): the gain-correction objective is non-convex in $g$, and quartic for $\mu_2=0$
-- statement:
--   Fix a non-negative image $\hat x$, let $\mu_1,\mu_2\ge0$, and suppose that at least one observed visibility $\tilde v_k$ is non-zero. Then the objective of eq. (12),
--
--   $$g\mapsto L_{\tilde v}(\hat x,g)+S_{\mu_1,\mu_2}(g),$$
--
--   is not a convex function of $g\in\mathbb{C}^{\sum_\alpha N_\alpha}$. If moreover $\mu_2=0$, it is a polynomial of total degree exactly $4$ in the real and imaginary parts of the gains.
--
--   **Formalization Note** The paper says the objective is "quartic and non-convex w.r.t. $g$" without restricting $\mu_2$. For $\mu_2>0$ the term $(|g_{\alpha l}|-|g_{\alpha,l-1}|)^2$ is not a polynomial, so "quartic" is stated only for $\mu_2=0$. Non-convexity is stated for all $\mu_1,\mu_2\ge0$. The hypothesis that some $\tilde v_k\ne0$ is implicit in the paper. Without it, and with $\mu_2=0$, the objective is convex. The Section 2.3 remark that non-convexity indicates local minima is not included.
-- source:
--   Ikeda, Nakazato, Tsukagoshi, Takeuchi and Yamaguchi, Solving Self-calibration of ALMA Data with an Optimization Method, arXiv:2412.03183v1 (2024), claim c002; Section 3.2, eqs. (12)-(13), PDF p. 3

import Mathlib
import Definitions.Def_Arxiv2412_03183_Basic

open Finset

namespace Arxiv2412_03183

theorem gain_objective_nonconvex {S : Type*} [Fintype S] [DecidableEq S] {N : S → ℕ}
    {M Nx Ny : ℕ} (D : ObsSetup S N M Nx Ny) (x : Image Nx Ny) (hx : x ∈ nonnegImages)
    (mu1 mu2 : ℝ) (hmu1 : 0 ≤ mu1) (hmu2 : 0 ≤ mu2) (hv : ∃ k, D.vobs k ≠ 0) :
    ¬ ConvexOn ℝ Set.univ (gainObjective D x mu1 mu2) ∧
    (mu2 = 0 → ∃ P : MvPolynomial (GainIdx N × Fin 2) ℝ, P.totalDegree = 4 ∧
      ∀ g : Gains N, MvPolynomial.eval (gainCoords g) P = gainObjective D x mu1 mu2 g) := by sorry

end Arxiv2412_03183

-- Prove2me | Theorems.Thm_Arxiv2412_03183_overall_problem_convex_in_x_nonconvex
-- name    : Arxiv2412_03183.overall_problem_convex_in_x_nonconvex
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T13:55:37.218817+00:00
-- url     : https://prove2.me/theorems/316c3168-4475-56d8-b73c-4173378e5436
-- title:
--   Eq. (14): the joint problem is convex in $x$ for fixed $g$ but non-convex overall
-- statement:
--   Let $\lambda_1,\lambda_2,\mu_1,\mu_2\ge0$ and suppose that at least one observed visibility $\tilde v_k$ is non-zero. Consider the joint problem of eq. (14),
--
--   $$\min_{x,g}\Big[L_{\tilde v}(x,g)+R_{\lambda_1,\lambda_2}(x)+S_{\mu_1,\mu_2}(g)\Big]\quad\text{subject to }x\ge0,\ \textstyle\sum_l|g_{\alpha l}|=N_\alpha.$$
--
--   (i) For every fixed feasible $g$, the problem in $x$ is convex: the objective is a convex function of $x$ on the convex set $\{x\ge0\}$.
--
--   (ii) The overall problem is not a convex problem: its feasible set of pairs $(x,g)$ is not convex.
--
--   (iii) The joint objective itself is not jointly convex in $(x,g)$: it is not a convex function on the convex set $\{x\ge0\}\times\mathbb{C}^{\sum_\alpha N_\alpha}$ (the gain constraint dropped).
--
--   **Formalization Note** "The overall problem is non-convex" is formalised twice. Part (ii) is the failure of `ConvexOn` on the feasible set of eq. (14); it holds for the trivial reason that the constraint $\sum_l|g_{\alpha l}|=N_\alpha$ defines a non-convex set ($g$ and $-g$ are feasible, their midpoint $0$ is not), whatever the objective. Part (iii) carries the content the paper intends, the coupling of $x$ and $g$ in $L_{\tilde v}$: the objective fails convexity on a convex domain. The hypothesis that some $\tilde v_k\ne0$ is implicit in the paper; without it, and with $\mu_2=0$, the objective is jointly convex and (iii) is false. It also guarantees a visibility, hence a gain, which (ii) needs.
-- source:
--   Ikeda, Nakazato, Tsukagoshi, Takeuchi and Yamaguchi, Solving Self-calibration of ALMA Data with an Optimization Method, arXiv:2412.03183v1 (2024), claim c005; Section 3.3, eq. (14), PDF p. 3

import Mathlib
import Definitions.Def_Arxiv2412_03183_Basic

open Finset

namespace Arxiv2412_03183

theorem overall_problem_convex_in_x_nonconvex {S : Type*} [Fintype S] [DecidableEq S]
    {N : S → ℕ} {M Nx Ny : ℕ} (D : ObsSetup S N M Nx Ny) (hv : ∃ k, D.vobs k ≠ 0)
    (lam1 lam2 mu1 mu2 : ℝ) (hlam1 : 0 ≤ lam1) (hlam2 : 0 ≤ lam2) (hmu1 : 0 ≤ mu1)
    (hmu2 : 0 ≤ mu2) :
    (∀ g ∈ gainFeasible N,
      ConvexOn ℝ nonnegImages (fun x => jointObjective D lam1 lam2 mu1 mu2 (x, g))) ∧
    ¬ ConvexOn ℝ (nonnegImages ×ˢ gainFeasible N) (jointObjective D lam1 lam2 mu1 mu2) ∧
    ¬ ConvexOn ℝ (nonnegImages ×ˢ (Set.univ : Set (Gains N)))
      (jointObjective D lam1 lam2 mu1 mu2) := by sorry

end Arxiv2412_03183

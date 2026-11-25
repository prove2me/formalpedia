-- Prove2me | Theorems.Thm_Arxiv2412_03183_imaging_problem_convex
-- name    : Arxiv2412_03183.imaging_problem_convex
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T13:43:31.012165+00:00
-- url     : https://prove2.me/theorems/f8f1e614-713a-5f43-bd2d-174e2f9f1d13
-- title:
--   Eq. (10): the imaging problem is convex in $x$
-- statement:
--   Fix gains $\hat g$ and positive coefficients $\lambda_1,\lambda_2>0$. Then the imaging problem of eq. (10),
--
--   $$\min_{x\ge0}\ \Big[L_{\tilde v}(x,\hat g)+\lambda_1\|x\|_1+\lambda_2\,\mathrm{TSV}(x)\Big],$$
--
--   is convex: the feasible set $\{x\in\mathbb{R}^{N_x\times N_y}:x\ge0\}$ is convex, and the objective is a convex function of $x$ on it.
-- source:
--   Ikeda, Nakazato, Tsukagoshi, Takeuchi and Yamaguchi, Solving Self-calibration of ALMA Data with an Optimization Method, arXiv:2412.03183v1 (2024), claim c023; Section 3.1, eqs. (8), (10), (11), PDF p. 3

import Mathlib
import Definitions.Def_Arxiv2412_03183_Basic

open Finset

namespace Arxiv2412_03183

theorem imaging_problem_convex {S : Type*} [Fintype S] [DecidableEq S] {N : S → ℕ}
    {M Nx Ny : ℕ} (D : ObsSetup S N M Nx Ny) (g : Gains N) (lam1 lam2 : ℝ)
    (hlam1 : 0 < lam1) (hlam2 : 0 < lam2) :
    ConvexOn ℝ nonnegImages (imagingObjective D lam1 lam2 g) := by sorry

end Arxiv2412_03183

-- Prove2me | Theorems.Thm_DecBilevel_SLDBO_lemma_A_1
-- name    : DecBilevel.SLDBO.lemma_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:05:30.157841+00:00
-- url     : https://prove2.me/theorems/978fa2d6-f040-48e9-942e-c35a5d2797e6
-- title:
--   Lemma A.1, p. 13 — the mixing matrix is nonexpansive and contracts the consensus error by ρ²
-- statement:
--   Let $W=(w_{ij})\in\mathbb R^{n\times n}$ and $\rho$ satisfy Assumption 2.2. For any $x_1,\dots,x_n\in\mathbb R^d$ with $\bar x=\frac1n\sum_ix_i$:
--
--   1. $$\sum_{i=1}^n\Big\|\sum_{j=1}^nw_{ij}x_j\Big\|^2\le\sum_{j=1}^n\|x_j\|^2;$$
--   2. $$\sum_{i=1}^n\Big\|\sum_{j=1}^nw_{ij}(x_j-\bar x)\Big\|^2\le\rho^2\sum_{i=1}^n\|x_i-\bar x\|^2.$$
--
--   Every consensus-error estimate of the paper uses one of these two inequalities.
--
--   **Formalization Note.** $\rho$ is any bound of $W$ on $\mathbf 1_n^\perp$ (Assumption 2.2 as encoded in the Setting module); the paper's eigenvalue $\rho$ is the least such bound.
-- source:
--   Dong, Ma, Yang, Yin, A Single-Loop Algorithm for Decentralized Bilevel Optimization, arXiv:2311.08945v3, p. 13, Lemma A.1

import Mathlib
import Definitions.Def_DecBilevel_SLDBO_Setting

namespace DecBilevel.SLDBO

theorem lemma_A_1 {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) (ρ : ℝ) (hA22 : Assumption22 W ρ)
    {d : ℕ} (z : Fin n → E d) :
    (∑ i, ‖∑ j, W i j • z j‖ ^ 2 ≤ ∑ j, ‖z j‖ ^ 2) ∧
    (∑ i, ‖∑ j, W i j • (z j - avg z)‖ ^ 2 ≤ ρ ^ 2 * ∑ i, ‖z i - avg z‖ ^ 2) := by sorry

end DecBilevel.SLDBO

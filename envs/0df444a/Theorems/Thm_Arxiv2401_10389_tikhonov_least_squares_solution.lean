-- Prove2me | Theorems.Thm_Arxiv2401_10389_tikhonov_least_squares_solution
-- name    : Arxiv2401_10389.tikhonov_least_squares_solution
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-26T13:15:32.857036+00:00
-- url     : https://prove2.me/theorems/a8b9a246-631c-5c8d-835d-f88bf219cf6e
-- title:
--   Eq. (15): the Tikhonov least-squares estimate $\hat u=(K^\dagger K+\alpha D_2^TD_2)^{-1}K^\dagger s$
-- statement:
--   Let $N_e\ge1$, $u_0\in\mathbb{C}^{N_e}$, a measured signal $s\in\mathbb{C}^{N_e}$, and $\alpha>0$. Let $K=K(\Gamma,u_0)$ be the operator of eq. (13a), and let $D_2$ be the $(N_e+1)\times(N_e+1)$ second-difference matrix of eq. (35). Assume $K^\dagger K+\alpha D_2^TD_2$ is invertible. Then the Tikhonov problem (14) with $L=D_2$,
--
--   $$\min_{v\in\mathbb{C}^{N_e+1}}\ \|s-Kv\|^2+\alpha\|D_2v\|^2,$$
--
--   has exactly one minimiser, namely
--
--   $$\hat u=(K^\dagger K+\alpha D_2^TD_2)^{-1}K^\dagger s.$$
--
--   This closed form is the estimate of the augmented aberration vector used in all experiments of the paper.
--
--   **Formalization Note** The invertibility of $K^\dagger K+\alpha D_2^TD_2$ is implicit in the paper's eq. (15) and is a hypothesis here. The minimisation runs over all of $\mathbb{C}^{N_e+1}$, as in eq. (14): the last entry of $v$ is not constrained to equal $1$. The paper uses $\alpha=0.01$. The statement says that the set of minimisers is exactly $\{\hat u\}$.
-- source:
--   Xing, Malescot, Martineau, Rungta and Provost, Inverse Problem Approach to Aberration Correction for in vivo Transcranial Imaging Based on a Sparse Representation of Contrast-enhanced Ultrasound Data, arXiv:2401.10389v3 (2025), claim c023; Section II.C, eqs. (14), (15), PDF p. 4; Supplemental materials C, eq. (35), PDF p. 17

import Mathlib
import Definitions.Def_Arxiv2401_10389_Basic

open Matrix Filter Topology Asymptotics

namespace Arxiv2401_10389

theorem tikhonov_least_squares_solution {Ne Ns : ℕ} (hNe : 1 ≤ Ne)
    (R : Matrix (Fin Ne) (Fin Ns) ℂ) (γ : Fin Ns → ℂ) (T : Matrix (Fin Ne) (Fin Ns) ℂ)
    (u₀ : Fin Ne → ℂ) (s : Fin Ne → ℂ) (α : ℝ) (hα : 0 < α)
    (hinv : (normalMatrix (linearOperator R γ T u₀) (secondDiffMatrix (Ne + 1)) α).det ≠ 0) :
    {v : Fin (Ne + 1) → ℂ | ∀ w, tikhonovObjective (linearOperator R γ T u₀)
        (secondDiffMatrix (Ne + 1)) α s v ≤
      tikhonovObjective (linearOperator R γ T u₀) (secondDiffMatrix (Ne + 1)) α s w} =
    {tikhonovSolution (linearOperator R γ T u₀) (secondDiffMatrix (Ne + 1)) α s} := by sorry

end Arxiv2401_10389

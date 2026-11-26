-- Prove2me | Theorems.Thm_Arxiv1803_10134_quasi_mode_expansion
-- name    : Arxiv1803_10134.quasi_mode_expansion
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-26T13:10:32.004274+00:00
-- url     : https://prove2.me/theorems/6dbdc40b-d191-4d1e-9e25-d7b9959d3d14
-- title:
--   Eqs. (16)-(17): expansion of the solution in quasi-modes
-- statement:
--   Let $\rho_0,c_p,c_s,\omega_0,\Gamma_0,\omega>0$, and let $\mathbf r_1,\dots,\mathbf r_N$ be pairwise distinct. Let $\Lambda_n$, $|R_n\rangle$, $\langle L_n|$ ($3N$ of each) be a biorthogonal eigensystem of $\hat G(\omega_0)$ (eqs. 13–15). Let $\omega_n=\omega_0-(\Gamma_0/2)\operatorname{Re}\Lambda_n$ and $\Gamma_n=\Gamma_0\operatorname{Im}\Lambda_n$, and assume $\omega-\omega_n+i\Gamma_n/2\neq0$ for every $n$. If $|u\rangle$ solves eq. (11) with $\hat G(\omega)$ replaced by $\hat G(\omega_0)$,
--   $$|u\rangle=|v\rangle+\frac{\alpha_0(\omega)}{B}\big[\hat G(\omega_0)-i\mathbb 1\big]|u\rangle,$$
--   then
--   $$|u(\omega)\rangle=\sum_nA_n(\omega)|R_n\rangle,\qquad A_n(\omega)=\frac{(-\Gamma_0/2)B}{\alpha_0(\omega)}\,\frac{\langle L_n|v\rangle}{\omega-\omega_n+i\Gamma_n/2}.$$
--
--   **Formalization Note** $B$ and $\alpha_0$ are evaluated at $\omega$, as in eq. (11). The condition $\omega-\omega_n+i\Gamma_n/2\neq0$ is implicit in eq. (17), which divides by this quantity. Biorthonormality of $3N$ pairs already implies that $\hat G(\omega_0)$ is diagonalizable, which the paper assumes without saying.
-- source:
--   Skipetrov and Beltukov, Anderson transition for elastic waves in three dimensions, arXiv:1803.10134v3 (2018), claim c008; Section III A, eqs. (11), (13)-(17), PDF pp. 4-5

import Mathlib
import Definitions.Def_Arxiv1803_10134_Basic

open Complex MeasureTheory Filter Topology

namespace Arxiv1803_10134

theorem quasi_mode_expansion {N : ℕ} (rho0 cp cs om0 gam0 om : ℝ) (hrho0 : 0 < rho0)
    (hcp : 0 < cp) (hcs : 0 < cs) (hom0 : 0 < om0) (hgam0 : 0 < gam0) (hom : 0 < om)
    (r : Fin N → Space) (hr : Function.Injective r)
    (lam : Idx N → ℂ) (R L : Idx N → Idx N → ℂ)
    (hRL : IsBiorthogonalEigensystem (greenMatrix rho0 cp cs om0 r) lam R L)
    (hden : ∀ n, ((om - qmFreq om0 gam0 (lam n) : ℝ) : ℂ) + I * ((qmWidth gam0 (lam n) / 2 : ℝ) : ℂ) ≠ 0)
    (u v : Idx N → ℂ)
    (hu : u = v + (polarizability (prefactorB rho0 cp cs om) om0 gam0 om /
          (prefactorB rho0 cp cs om : ℂ)) •
        (greenMatrix rho0 cp cs om0 r - I • (1 : Matrix (Idx N) (Idx N) ℂ)).mulVec u) :
    u = ∑ n, ((((-gam0 / 2 : ℝ) : ℂ) * (prefactorB rho0 cp cs om : ℂ) /
          polarizability (prefactorB rho0 cp cs om) om0 gam0 om) *
        ((L n ⬝ᵥ v) / (((om - qmFreq om0 gam0 (lam n) : ℝ) : ℂ) +
          I * ((qmWidth gam0 (lam n) / 2 : ℝ) : ℂ)))) • R n := by sorry

end Arxiv1803_10134

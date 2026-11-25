-- Prove2me | Theorems.Thm_Arxiv2205_09423_normalized_blocks_single_scattering
-- name    : Arxiv2205_09423.normalized_blocks_single_scattering
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T11:54:50.260431+00:00
-- url     : https://prove2.me/theorems/2560c9d4-c130-456b-8c7b-6ae19b250a45
-- title:
--   Eqs. (14)–(15): the normalized transmission and reflection blocks
-- statement:
--   Let $k>0$ and let $\boldsymbol\kappa_{-N_k},\dots,\boldsymbol\kappa_{N_k}$ be a mode set as in Section 2.1 ($|\boldsymbol\kappa_i|<k$, $\boldsymbol\kappa_{-i}=-\boldsymbol\kappa_i$, distinct, $w=\pi k^2/(2N_k+1)$). Consider $N$ particles with centres $\mathbf r_p\in\mathbb R^3$ and far-field amplitude matrices $\mathbf A_p$, and let $\mathbf t_{(j,i)}$, $\mathbf r_{(j,i)}$ be the reductions (12)–(13) in the polar bases (11) of the discretized matrices
--
--   $$\mathbf t(\boldsymbol\kappa_j,\boldsymbol\kappa_i)=\frac{\delta_{ij}}{w}\mathbb I_3+\frac{1}{2\pi kk_{jz}}\sum_{p=1}^N\mathbf A_p(\mathbf u_j,\mathbf u_i)e^{i(\mathbf k_i-\mathbf k_j)\cdot\mathbf r_p},\qquad \mathbf r(\boldsymbol\kappa_j,\boldsymbol\kappa_i)=\frac{1}{2\pi kk_{jz}}\sum_{p=1}^N\mathbf A_p(\widetilde{\mathbf u}_j,\mathbf u_i)e^{i(\mathbf k_i-\widetilde{\mathbf k}_j)\cdot\mathbf r_p}.$$
--
--   Then for all modes $i,j$
--
--   $$\sqrt{\frac{k_{jz}}{k_{iz}}}\,\mathbf t_{(j,i)}w=\delta_{ij}\mathbb I_2+C_{ji}\sum_{p=1}^N\mathbf A^t_{p(j,i)}e^{i(\mathbf k_i-\mathbf k_j)\cdot\mathbf r_p},\qquad \sqrt{\frac{k_{jz}}{k_{iz}}}\,\mathbf r_{(j,i)}w=C_{ji}\sum_{p=1}^N\mathbf A^r_{p(j,i)}e^{i(\mathbf k_i-\widetilde{\mathbf k}_j)\cdot\mathbf r_p},$$
--
--   with $C_{ji}=w/(2\pi k\sqrt{k_{jz}k_{iz}})$, where $\mathbf A^t_{p(j,i)}$ and $\mathbf A^r_{p(j,i)}$ are the reductions of $\mathbf A_p(\mathbf u_j,\mathbf u_i)$ and $\mathbf A_p(\widetilde{\mathbf u}_j,\mathbf u_i)$ in the same bases.
--
--   These are the normalized blocks from which the scattering matrix (17) is assembled.
--
--   **Formalization Note** The single-scattering, far-field and cubature approximations that lead to the discretized matrices (Eqs. 2–10) are modelling steps. Eqs. (9)–(10) are taken as the definitions of $\mathbf t$ and $\mathbf r$, and the statement is the identity (14)–(15) that follows from them.
-- source:
--   Byrnes and Foreman, Random matrix theory of polarized light scattering in disordered media, arXiv:2205.09423v1 (2022), claim c001; Section 2.1, Eqs. (9)-(15), PDF pp. 5-6

import Mathlib
import Definitions.Def_Arxiv2205_09423_Basic

open MeasureTheory ProbabilityTheory Matrix

namespace Arxiv2205_09423

theorem normalized_blocks_single_scattering {Nk N : ℕ} (K : ModeSet Nk) (hK : K.IsValid)
    (A : Fin N → Amp) (r : Fin N → Fin 3 → ℝ) (j i : Fin (2 * Nk + 1)) :
    tNorm K A r j i = tbar K A r j i ∧ rNorm K A r j i = rbar K A r j i := by sorry

end Arxiv2205_09423

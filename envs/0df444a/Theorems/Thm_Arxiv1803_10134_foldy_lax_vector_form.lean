-- Prove2me | Theorems.Thm_Arxiv1803_10134_foldy_lax_vector_form
-- name    : Arxiv1803_10134.foldy_lax_vector_form
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-26T13:09:19.46947+00:00
-- url     : https://prove2.me/theorems/ce3a6ac1-6698-49f5-9e86-c6dbace15fed
-- title:
--   Eqs. (11)-(12): vector form of the Foldy-Lax equations and the Green's matrix
-- statement:
--   Let $\rho_0,c_p,c_s,\omega,\omega_0,\Gamma_0>0$, and let $\mathbf r_1,\dots,\mathbf r_N\in\mathbb R^3$ be pairwise distinct. Then:
--
--   1. For all $|u\rangle,|v\rangle\in\mathbb C^{3N}$, the Foldy–Lax equations (9) hold if and only if
--   $$|u\rangle=|v\rangle+\frac{\alpha_0(\omega)}{B}\big[\hat G(\omega)-i\mathbb 1\big]|u\rangle .\qquad(11)$$
--   2. The blocks of the Green's matrix are, with $\mathbf r_{mn}=\mathbf r_m-\mathbf r_n$ and $r_{mn}=|\mathbf r_{mn}|$,
--   $$\hat G_{mn}(\omega)=i\delta_{mn}\mathbb 1+\frac{1-\delta_{mn}}{1+2(c_p/c_s)^3}\Big\{\frac{e^{ik_pr_{mn}}}{k_pr_{mn}}\big[\mathbb 1-\hat F(k_p\mathbf r_{mn})\big]+2\Big(\frac{c_p}{c_s}\Big)^3\frac{e^{ik_sr_{mn}}}{k_sr_{mn}}\big[\mathbb 1+\tfrac12\hat F(k_s\mathbf r_{mn})\big]\Big\}.\qquad(12)$$
--   3. In particular $\hat G(\omega)$ does not depend on the density $\rho_0$. It depends only on $\omega$, $c_p$, $c_s$ and the positions.
--
--   **Formalization Note** The Green's matrix is defined by the first line of eq. (12). The second line is part of the statement, and it holds only with $B$ read as $12\pi\rho_0c_p^3/(\omega[1+2(c_p/c_s)^3])$. The scatterers are taken pairwise distinct so that every $r_{mn}$ with $m\neq n$ is positive.
-- source:
--   Skipetrov and Beltukov, Anderson transition for elastic waves in three dimensions, arXiv:1803.10134v3 (2018), claim c007; Section III A, eqs. (9), (11), (12), PDF p. 4

import Mathlib
import Definitions.Def_Arxiv1803_10134_Basic

open Complex MeasureTheory Filter Topology

namespace Arxiv1803_10134

theorem foldy_lax_vector_form {N : ℕ} (rho0 cp cs om om0 gam0 : ℝ) (hrho0 : 0 < rho0)
    (hcp : 0 < cp) (hcs : 0 < cs) (hom : 0 < om) (hom0 : 0 < om0) (hgam0 : 0 < gam0)
    (r : Fin N → Space) (hr : Function.Injective r) :
    (∀ u v : Idx N → ℂ, IsFoldyLaxSolution rho0 cp cs om0 gam0 om r u v ↔
      u = v + (polarizability (prefactorB rho0 cp cs om) om0 gam0 om /
          (prefactorB rho0 cp cs om : ℂ)) •
        (greenMatrix rho0 cp cs om r - I • (1 : Matrix (Idx N) (Idx N) ℂ)).mulVec u) ∧
    (∀ (m n : Fin N) (a b : Fin 3), greenMatrix rho0 cp cs om r (m, a) (n, b) =
      (if m = n then (if a = b then I else 0) else 0) +
      (if m = n then 0 else ((1 / (1 + 2 * (cp / cs) ^ 3) : ℝ) : ℂ) *
        (compressivePart cp om (r m - r n) a b +
          ((2 * (cp / cs) ^ 3 : ℝ) : ℂ) * shearPart cs om (r m - r n) a b))) ∧
    (∀ rho0' : ℝ, 0 < rho0' → greenMatrix rho0' cp cs om r = greenMatrix rho0 cp cs om r) := by sorry

end Arxiv1803_10134

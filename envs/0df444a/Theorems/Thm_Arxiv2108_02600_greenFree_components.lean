-- Prove2me | Theorems.Thm_Arxiv2108_02600_greenFree_components
-- name    : Arxiv2108_02600.greenFree_components
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T09:40:01.200864+00:00
-- url     : https://prove2.me/theorems/05aa03ab-cfe9-4523-aa55-d9bd5ebd5150
-- title:
--   Eq. (3.7): componentwise form of the free-space Green's tensor
-- statement:
--   Let $x\ne y$ in $\mathbb R^2$ and $r=|x-y|$. The entries of the free-space Green's tensor $G(x,y)=\frac1\mu\Phi(x,y,\kappa_s)I+\omega^{-2}\nabla_x\nabla_x^\top(\Phi(x,y,\kappa_s)-\Phi(x,y,\kappa_p))$ of the Navier equation are, for $j,k=1,2$,
--
--   $$G_{jk}(x,y)=\Big[\frac{i}{4\mu}H^{(1)}_0(\kappa_sr)-\frac{i}{4\omega^2}\,\frac{\kappa_sH^{(1)}_1(\kappa_sr)-\kappa_pH^{(1)}_1(\kappa_pr)}{r}\Big]\delta_{jk}+\frac{i}{4\omega^2}\,\frac{\kappa_s^2H^{(1)}_2(\kappa_sr)-\kappa_p^2H^{(1)}_2(\kappa_pr)}{r^2}(x_j-y_j)(x_k-y_k).$$
--
--   This is the starting point of the singularity analysis of Section 3.
-- source:
--   J. Li, X. Liu, B. Zhang and H. Zhang, The Nyström method for elastic wave scattering by unbounded rough surfaces, arXiv:2108.02600v1 (2021), claim c001; Section 3.1, eq. (3.7) (from definition (2.7)), PDF p. 8

import Mathlib
import Definitions.Def_Arxiv2108_02600_Basic

open MeasureTheory Filter Topology

namespace Arxiv2108_02600

theorem greenFree_components (P : Lame) (x y : Pt) (hxy : x ≠ y) (j k : Fin 2) :
    let r := dist2 x y
    greenFree P x y j k =
      (if j = k then
          Complex.I / (4 * (P.mu : ℂ)) * hankel1 0 (P.ks * r) -
            Complex.I / (4 * (P.omega : ℂ) ^ 2) *
              ((P.ks : ℂ) * hankel1 1 (P.ks * r) - (P.kp : ℂ) * hankel1 1 (P.kp * r)) / (r : ℂ)
        else 0) +
        Complex.I / (4 * (P.omega : ℂ) ^ 2) *
          ((P.ks : ℂ) ^ 2 * hankel1 2 (P.ks * r) - (P.kp : ℂ) ^ 2 * hankel1 2 (P.kp * r)) /
            (r : ℂ) ^ 2 * (((x j - y j) * (x k - y k) : ℝ) : ℂ) := by sorry

end Arxiv2108_02600

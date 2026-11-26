-- Prove2me | Theorems.Thm_Arxiv1504_01000_hellinger_gamma_closed_form
-- name    : Arxiv1504_01000.hellinger_gamma_closed_form
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-24T18:13:19.52037+00:00
-- url     : https://prove2.me/theorems/284e858a-90c8-447d-bce9-caaacf8edff2
-- title:
--   Eq. (6) (as corrected by eq. (9)): Hellinger distance between two multilook intensity laws
-- statement:
--   Let $L>0$ and $\sigma_i,\sigma_j>0$. Let $f_i$ and $f_j$ be the densities of the multilook intensity laws, the Gamma distributions with shape $L$ and means $\sigma_i^2$ and $\sigma_j^2$. Then $\sqrt{f_if_j}$ is integrable on $\mathbb{R}$, and the Hellinger distance $d_H=1-\int\sqrt{f_if_j}$ is
--
--   $$d_H(\sigma_i^2,\sigma_j^2)=1-\left[\frac{2\sigma_i\sigma_j}{\sigma_i^2+\sigma_j^2}\right]^L.$$
--
--   This is the closed form on which the orientation-angle estimator of eq. (9) rests.
--
--   **Formalization Note** As printed, eq. (6) has $\sigma_i\sigma_j/(2(\sigma_i^2+\sigma_j^2))$ inside the bracket. That expression gives $1-(1/4)^L\neq0$ for identical distributions, so it is not the Hellinger distance the sentence after eq. (6) says it is. The statement uses the form with the factor $2$ in the numerator. This is the correct value of that Hellinger distance, and it is the form the paper itself uses in eq. (9). Integrability is stated explicitly so that the integral is not a default value.
-- source:
--   Bhattacharya, Muhuri, De, Manickam and Frery, Modifying the Yamaguchi Four-Component Decomposition Scattering Powers Using a Stochastic Distance, arXiv:1504.01000v1 (2015), claim c022; Sec. II (Stochastic Distances), eq. (6) and the sentence after it, PDF p. 3; corrected form as used in eq. (9), Sec. III, PDF pp. 3-4

import Mathlib
import Definitions.Def_Arxiv1504_01000_Basic

open MeasureTheory Filter Topology
open scoped ComplexOrder

namespace Arxiv1504_01000

theorem hellinger_gamma_closed_form (L σi σj : ℝ) (hL : 0 < L) (hi : 0 < σi) (hj : 0 < σj) :
    Integrable (fun x => Real.sqrt (intensityPDF L (σi ^ 2) x * intensityPDF L (σj ^ 2) x)) ∧
    hellingerDist (intensityPDF L (σi ^ 2)) (intensityPDF L (σj ^ 2)) =
      1 - (2 * σi * σj / (σi ^ 2 + σj ^ 2)) ^ L := by sorry

end Arxiv1504_01000

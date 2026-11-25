-- Prove2me | Theorems.Thm_Arxiv2105_07250_collinear_receivers_same_frequency
-- name    : Arxiv2105_07250.collinear_receivers_same_frequency
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T09:29:34.926058+00:00
-- url     : https://prove2.me/theorems/255226e1-1172-4b6f-a9f2-851741fe1fec
-- title:
--   Section 4.3: receivers collinear with the source record the same frequency
-- statement:
--   Let $c>0$, $v\in\mathbb{R}^2$ with $0<|v|<c$, $\tilde\omega\in\mathbb{R}$, and let the receivers $x_A,x_B$ lie strictly on the same side of the source line $S=\mathbb{R}v$. If at time $t'$ the instantaneous source position $vt'$ is collinear with $x_A$ and $x_B$, then $\theta_{x_A}(t')=\theta_{x_B}(t')$, and so the two receivers record the same frequency: $\breve\omega(x_A,t')=\breve\omega(x_B,t')$.
--
--   **Formalization Note** Collinearity is written as $x_B-vt'=\lambda(x_A-vt')$ for some real $\lambda$. "Same side of $S$" is written as $\det(v,x_A)\det(v,x_B)>0$. The paper does not state this condition, but its geometry has it: the receivers lie on one side of the road, and if they lay on opposite sides the two angles would be supplementary rather than equal. The other parts of the paper's paragraph (spurious contributions minimised, the stationary-phase point lies in the Fresnel zone) are not mathematical statements and are not included.
-- source:
--   D. Ayala-Garcia, A. Curtis and M. Branicki, Seismic Interferometry from Correlated Noise Sources, arXiv:2105.07250v2 (2021), claim c035; Section 4.3, first paragraph after the steps, with eq. (5), PDF p. 23

import Mathlib
import Definitions.Def_Arxiv2105_07250_Basic

open MeasureTheory ProbabilityTheory Filter Topology

namespace Arxiv2105_07250

theorem collinear_receivers_same_frequency (c : ℝ) (hc : 0 < c) (v : Plane) (hv0 : v ≠ 0)
    (hv : ‖v‖ < c) (wt : ℝ) (xA xB : Plane)
    (hside : 0 < (v 0 * xA 1 - v 1 * xA 0) * (v 0 * xB 1 - v 1 * xB 0)) (t' : ℝ)
    (hcol : ∃ l : ℝ, xB - t' • v = l • (xA - t' • v)) :
    cosTheta xA v t' = cosTheta xB v t' ∧
      recordedFrequency c wt xA v t' = recordedFrequency c wt xB v t' := by sorry

end Arxiv2105_07250

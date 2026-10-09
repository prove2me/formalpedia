-- Prove2me | Theorems.Thm_DistCov_Hilbert_theorem_3_16
-- name    : DistCov.Hilbert.theorem_3_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:28:16.692618+00:00
-- url     : https://prove2.me/theorems/fc2f6b07-f565-460e-ac61-3897b4b28393
-- title:
--   Theorem 3.16 — every separable Hilbert space is of strong negative type
-- statement:
--   Let $H$ be a separable real Hilbert space with its norm distance $d(x,y)=\|x-y\|$ and its Borel $\sigma$-field. Then $H$ is of **strong negative type**:
--
--   1. $H$ has negative type: $\sum_{i,j}\alpha_i\alpha_j\|x_i-x_j\|\le0$ whenever $\sum_i\alpha_i=0$;
--   2. for Borel probability measures $\mu_1,\mu_2$ on $H$ with finite first moments,
--   $$D(\mu_1-\mu_2)=0\quad\Longrightarrow\quad\mu_1=\mu_2 .$$
--
--   Combined with Theorem 3.11 of the paper, this shows that zero distance covariance characterizes independence for random variables taking values in separable Hilbert spaces, which answers a question of Kosorok (2009).
--
--   **Formalization Note.** Hilbert spaces are real, as the paper assumes (Errata (viii), p. 27); a complex Hilbert space has the same distances as its realification, so the real case is the theorem. Separability is `SecondCountableTopology`, which is equivalent for metric spaces. $D(\mu_1-\mu_2)$ is the energy expansion $E(\mu_1,\mu_1)-2E(\mu_1,\mu_2)+E(\mu_2,\mu_2)$ of the Setting file, and strong negative type is defined by (3.1) and (3.3), not through an embedding or a barycenter map.
-- source:
--   Lyons, Distance covariance in metric spaces, arXiv:1106.5758 (version of 19 Dec. 2020), p. 18, Theorem 3.16; Errata (viii), p. 27

import Mathlib
import Definitions.Def_DistCov_Hilbert_Setting

namespace DistCov.Hilbert

open MeasureTheory ProbabilityTheory

theorem theorem_3_16 (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] :
    DistCov.Indep.StrongNegType H := by sorry

end DistCov.Hilbert

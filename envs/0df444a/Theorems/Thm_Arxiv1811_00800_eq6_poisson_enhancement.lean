-- Prove2me | Theorems.Thm_Arxiv1811_00800_eq6_poisson_enhancement
-- name    : Arxiv1811_00800.eq6_poisson_enhancement
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T20:45:32.299188+00:00
-- url     : https://prove2.me/theorems/08019f8f-9ad9-5d70-bc3c-c69aa3c431bb
-- title:
--   Eq. (6): for Poisson loop numbers, $E(\alpha)=1+\operatorname{Re}\exp[\beta(e^{4i\pi\alpha}-1)]$
-- statement:
--   Let $\beta\ge0$ and $\alpha\in\mathbb{R}$. If the loop numbers are Poisson distributed, $p_n=\frac{\beta^ne^{-\beta}}{n!}$, then the sum of Eq. (5) is
--
--   $$\sum_{n\in\mathbb{N}}\frac{\beta^ne^{-\beta}}{n!}\left[1+\cos(4\pi n\alpha)\right]=1+\operatorname{Re}\left\{\exp\left[\beta\left(e^{4i\pi\alpha}-1\right)\right]\right\}.$$
--
--   This is the model the paper fits to its data, with $\beta=\langle n\rangle$ the mean number of loops at a given travel time.
--
--   **Formalization Note** The Poisson weights are Mathlib's Poisson distribution with rate $\beta$, $p_n=\mathrm{Po}(\beta)(\{n\})$.
-- source:
--   Aubry and Roux, Topological Effects of a Vorticity Filament on the Coherent Backscattering Cone, arXiv:1811.00800v2 (2019), claim c008; main text, after Eq. (5), Eq. (6), PDF p. 4

import Mathlib
import Definitions.Def_Arxiv1811_00800_Basic

open MeasureTheory ProbabilityTheory Complex

namespace Arxiv1811_00800

theorem eq6_poisson_enhancement (beta : NNReal) (alpha : ℝ) :
    loopEnhancement (fun n => (poissonMeasure beta).real {n}) alpha =
      poissonEnhancement beta alpha := by sorry

end Arxiv1811_00800

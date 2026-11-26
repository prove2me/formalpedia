-- Prove2me | Theorems.Thm_Arxiv1811_00800_eq6_periodic_rebirth
-- name    : Arxiv1811_00800.eq6_periodic_rebirth
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T20:46:42.20443+00:00
-- url     : https://prove2.me/theorems/53c151cc-b488-4191-96d6-f994ad9d444b
-- title:
--   Eq. (6), rebirth: $E$ is $0.5$-periodic and $E(0.5)=2$
-- statement:
--   Let $\beta\ge0$ and let $E_\beta(\alpha)=1+\operatorname{Re}\exp[\beta(e^{4i\pi\alpha}-1)]$ be the Poisson model of Eq. (6). Then $E_\beta$ is periodic in $\alpha$ with period $\tfrac12$, and
--
--   $$E_\beta\left(\tfrac12\right)=2.$$
--
--   The value $2$ is the full enhancement of a reciprocal medium: the paper calls it a rebirth of the coherent backscattering cone although reciprocity is broken.
--
--   **Formalization Note** "$0.5$ periodic" is stated as periodicity with period $\tfrac12$; for $\beta=0$ the function is constant. The paper's comparison with solid rotation and Faraday rotation, quoted from other works, is not part of the statement.
-- source:
--   Aubry and Roux, Topological Effects of a Vorticity Filament on the Coherent Backscattering Cone, arXiv:1811.00800v2 (2019), claim c011; main text, paragraph after Fig. 4, and Fig. 4(b), PDF p. 4

import Mathlib
import Definitions.Def_Arxiv1811_00800_Basic

open MeasureTheory ProbabilityTheory Complex

namespace Arxiv1811_00800

theorem eq6_periodic_rebirth (beta : NNReal) :
    Function.Periodic (poissonEnhancement beta) (1 / 2) ∧ poissonEnhancement beta (1 / 2) = 2 := by sorry

end Arxiv1811_00800

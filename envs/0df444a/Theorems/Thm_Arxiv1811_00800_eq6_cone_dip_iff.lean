-- Prove2me | Theorems.Thm_Arxiv1811_00800_eq6_cone_dip_iff
-- name    : Arxiv1811_00800.eq6_cone_dip_iff
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T20:46:07.891471+00:00
-- url     : https://prove2.me/theorems/42e971ec-12e3-4e51-9f6c-9dfdab60c86f
-- title:
--   Eq. (6), cone dip (precise form): $E(\alpha)<1$ for some intermediate $\alpha$ if and only if $\beta>\pi/2$
-- statement:
--   Let $\beta\ge0$ and let $E_\beta(\alpha)=1+\operatorname{Re}\exp[\beta(e^{4i\pi\alpha}-1)]$ be the Poisson model of Eq. (6). The model has a cone dip, $E_\beta(\alpha)<1$, at some intermediate value $0<\alpha<\tfrac12$ if and only if
--
--   $$\beta>\frac{\pi}{2}.$$
--
--   **Formalization Note** The paper says that the model confirms a dip $E(\alpha)<1$ at intermediate $\alpha$ for the mean loop numbers fitted to its data, and gives no condition on $\beta$. Since $E_\beta(\alpha)-1=e^{-\beta(1-\cos4\pi\alpha)}\cos(\beta\sin4\pi\alpha)$, a dip exists only for $\beta>\pi/2$; the statement makes this condition explicit. "Intermediate" is read as $0<\alpha<\tfrac12$, the open period interval, at whose ends $E_\beta=2$.
-- source:
--   Aubry and Roux, Topological Effects of a Vorticity Filament on the Coherent Backscattering Cone, arXiv:1811.00800v2 (2019), claim c010; main text, paragraph after Fig. 4, PDF p. 4

import Mathlib
import Definitions.Def_Arxiv1811_00800_Basic

open MeasureTheory ProbabilityTheory Complex

namespace Arxiv1811_00800

theorem eq6_cone_dip_iff (beta : NNReal) :
    (∃ alpha ∈ Set.Ioo (0 : ℝ) (1 / 2), poissonEnhancement beta alpha < 1) ↔
      Real.pi / 2 < (beta : ℝ) := by sorry

end Arxiv1811_00800

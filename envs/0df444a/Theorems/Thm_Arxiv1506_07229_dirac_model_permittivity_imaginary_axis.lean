-- Prove2me | Theorems.Thm_Arxiv1506_07229_dirac_model_permittivity_imaginary_axis
-- name    : Arxiv1506_07229.dirac_model_permittivity_imaginary_axis
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T02:04:42.32303+00:00
-- url     : https://prove2.me/theorems/6601ea21-2938-4af2-b127-bcace592cafe
-- title:
--   Eq. (A1): permittivity of strictly-2D graphene at imaginary frequency
-- statement:
--   Consider undoped graphene viewed as a strictly two-dimensional system of massless Dirac electrons with Fermi velocity $v>0$ and spin-valley degeneracy $4$. Let $\chi(q,iu)$ be its RPA (non-interacting) density-response function at in-plane wave number $q>0$ and imaginary frequency $iu$, $u\in\mathbb{R}$. Then the permittivity $\varepsilon(q,iu)=1-\frac{2\pi}{q}\chi(q,iu)$ is
--
--   $$\varepsilon(q,iu)=1+\frac{\pi q}{2\sqrt{u^2+(qv)^2}}\qquad\text{(Eq. (A1))}.$$
--
--   Equivalently, $\chi(q,iu)=-q^2/(4\sqrt{u^2+v^2q^2})$. This is half the density response printed in Eq. (2) of Dobson, White and Rubio (2006), as the paper states.
--
--   **Formalization Note** The paper quotes (A1) from Dobson et al. and Wunsch et al. as the small-$q$ form for real graphene. In the Dirac model it holds for every $q>0$, and it is stated so here. The model response is written as the explicit integral over $\mathbb{R}^2$ given in the definitions, with the wave vector along the first axis.
-- source:
--   V. U. Nazarov, Negative static permittivity and violation of Kramers-Kronig relations in quasi-two-dimensional crystals, arXiv:1506.07229v3 (2015), claim c016; Appendix A, Eq. (A1), PDF p. 6

import Mathlib
import Definitions.Def_Arxiv1506_07229_Basic

open MeasureTheory Filter Topology Real ComplexConjugate

namespace Arxiv1506_07229

theorem dirac_model_permittivity_imaginary_axis (v q u : ℝ) (hv : 0 < v) (hq : 0 < q) :
    dirac2DEps v q u = 1 + π * q / (2 * Real.sqrt (u ^ 2 + (q * v) ^ 2)) := by sorry

end Arxiv1506_07229

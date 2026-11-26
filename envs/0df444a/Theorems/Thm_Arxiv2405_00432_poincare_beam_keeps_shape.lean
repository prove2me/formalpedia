-- Prove2me | Theorems.Thm_Arxiv2405_00432_poincare_beam_keeps_shape
-- name    : Arxiv2405_00432.poincare_beam_keeps_shape
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-26T12:52:58.599801+00:00
-- url     : https://prove2.me/theorems/6411e5b7-3c0f-59de-9946-434fd2c508d4
-- title:
--   Eq. (10): the Poincaré beam keeps its shape on propagation
-- statement:
--   Let $\mathrm{LG}_1^0$ and $\mathrm{LG}_0^2$ be paraxial Laguerre-Gaussian modes with a common waist $w_0>0$ at $z=0$ and common wavelength $\lambda>0$, and let $|\Psi\rangle=\mathrm{LG}_1^0|h\rangle+\mathrm{LG}_0^2|v\rangle$ be the Poincaré beam of eq. (10). Then both modes have mode order $N=2p+|\ell|=2$, they have the same Gouy phase in every plane $z$ (by the definition above it is $(N+1)\arctan(z/z_R)=3\arctan(z/z_R)$), and the beam keeps its intensity and polarization profile on propagation apart from an overall change of size: for all $r\ge0$, $\varphi$ and $z$,
--   $$S\big(\Psi(r,\varphi,z)\big)=\Big(\frac{w_0}{w(z)}\Big)^2\,S\Big(\Psi\Big(\frac{w_0}{w(z)}\,r,\varphi,0\Big)\Big),$$
--   where $S$ is the Stokes vector and $w(z)=w_0\sqrt{1+(z/z_R)^2}$.
--
--   **Formalization Note** The paper states the conclusion in words; "keeps its shape apart from an overall change of size" is stated as the scaling law of the full Stokes vector, which contains both the intensity $S_0$ and the polarization profile $S/S_0$. The common waist and waist position of the two modes are not written in the paper and are assumed, as the conclusion needs them. The overall factor $(w_0/w)^2$ is the decrease in peak intensity that comes with the increase in size.
-- source:
--   McWilliam, Al Khafaji, Svensson, Pádua and Franke-Arnold, Dynamic Mueller matrix polarimetry using generalized measurements, arXiv:2405.00432v1 (2024), claim c016; Section 4, eq. (10) and the sentence after it, PDF p. 8

import Mathlib
import Definitions.Def_Arxiv2405_00432_Basic

open Matrix

namespace Arxiv2405_00432

theorem poincare_beam_keeps_shape (w0 lam : ℝ) (hw0 : 0 < w0) (hlam : 0 < lam) :
    modeOrder 1 0 = 2 ∧ modeOrder 0 2 = 2 ∧
    (∀ z : ℝ, gouyPhase 1 0 w0 lam z = gouyPhase 0 2 w0 lam z) ∧
    (∀ r φ z : ℝ, 0 ≤ r →
      stokes (poincareBeam w0 lam r φ z) =
        (w0 / beamWidth w0 lam z) ^ 2 •
          stokes (poincareBeam w0 lam (r * w0 / beamWidth w0 lam z) φ 0)) := by sorry

end Arxiv2405_00432

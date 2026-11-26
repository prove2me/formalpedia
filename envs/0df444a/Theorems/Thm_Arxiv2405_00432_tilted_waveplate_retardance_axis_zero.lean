-- Prove2me | Theorems.Thm_Arxiv2405_00432_tilted_waveplate_retardance_axis_zero
-- name    : Arxiv2405_00432.tilted_waveplate_retardance_axis_zero
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-26T12:53:51.47387+00:00
-- url     : https://prove2.me/theorems/558c4984-7017-5013-8a88-b57585899401
-- title:
--   Eqs. (15)-(16): the retardance of a tilted waveplate with fast axis at 0°
-- statement:
--   Let $T>0$ be the thickness of a waveplate, $\lambda>0$ the wavelength, $n_o,n_e>0$ the ordinary and extraordinary refractive indices, and $\delta_T(\theta,\alpha)$ the theoretical retardance of eq. (15) at fast-axis angle $\theta$ and angle of incidence $\alpha$. For a fast axis at $0^\circ$, for every $\alpha$,
--   $$\delta_T(0,\alpha)=\frac{2\pi T}{\lambda}\left(\sqrt{n_e^2\Big(1-\frac{\sin^2\alpha}{n_o^2}\Big)}-\sqrt{n_o^2-\sin^2\alpha}\right),$$
--   which is eq. (16), the formula fitted to the measured retardance of the tilted quarter-wave plate.
--
--   **Formalization Note** Eq. (15) itself is taken from the literature (Gu et al. 2018, modified for a multi-order plate) without derivation; it enters as a definition, and only its reduction to eq. (16) is stated.
-- source:
--   McWilliam, Al Khafaji, Svensson, Pádua and Franke-Arnold, Dynamic Mueller matrix polarimetry using generalized measurements, arXiv:2405.00432v1 (2024), claim c010; Section 4.2, eqs. (15), (16), PDF p. 12

import Mathlib
import Definitions.Def_Arxiv2405_00432_Basic

open Matrix

namespace Arxiv2405_00432

theorem tilted_waveplate_retardance_axis_zero (T lam no ne α : ℝ) (hT : 0 < T) (hlam : 0 < lam)
    (hno : 0 < no) (hne : 0 < ne) :
    theoryRetardance T lam no ne 0 α =
      2 * Real.pi * T / lam *
        (Real.sqrt (ne ^ 2 * (1 - Real.sin α ^ 2 / no ^ 2)) - Real.sqrt (no ^ 2 - Real.sin α ^ 2)) := by sorry

end Arxiv2405_00432

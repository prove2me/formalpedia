-- Prove2me | Theorems.Thm_Arxiv1110_5134_stokes_axis_choice_invariance
-- name    : Arxiv1110_5134.stokes_axis_choice_invariance
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T09:07:50.876276+00:00
-- url     : https://prove2.me/theorems/a062ebd7-cb12-412f-acbc-39af328f5a34
-- title:
--   Appendix A (after Eq. 68): long-axis and short-axis definitions give the same Stokes vector
-- statement:
--   The Stokes vector of Eq. (1) is invariant under the change of description $\psi'=\psi+\pi/2$, $\tan\chi'=1/\tan\chi$ (for $\tan\chi\ne0$):
--
--   $$\big(I,\ I\cos2\chi'\cos2\psi',\ I\cos2\chi'\sin2\psi',\ I\sin2\chi'\big)=\big(I,\ I\cos2\chi\cos2\psi,\ I\cos2\chi\sin2\psi,\ I\sin2\chi\big).$$
--
--   So, within one reference frame, the long-axis and short-axis definitions of the polarization ellipse give the same Stokes parameters.
-- source:
--   Zhao, Tan and Liu, On the Derivation of Vector Radiative Transfer Equation for Polarized Radiative Transport in Graded Index Media, arXiv:1110.5134v1 (2011), claim c022; Appendix A, text after Eq. (68), PDF p. 26

import Mathlib
import Definitions.Def_Arxiv1110_5134_Basic

open MeasureTheory Filter Topology
open scoped Matrix

namespace Arxiv1110_5134

theorem stokes_axis_choice_invariance (I χ ψ χ' : ℝ) (hχ : Real.tan χ ≠ 0)
    (hχ' : Real.tan χ' = 1 / Real.tan χ) :
    stokesVec I χ' (ψ + Real.pi / 2) = stokesVec I χ ψ := by sorry

end Arxiv1110_5134

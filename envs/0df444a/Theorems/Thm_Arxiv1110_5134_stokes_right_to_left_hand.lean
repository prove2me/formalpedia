-- Prove2me | Theorems.Thm_Arxiv1110_5134_stokes_right_to_left_hand
-- name    : Arxiv1110_5134.stokes_right_to_left_hand
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-24T09:06:31.803869+00:00
-- url     : https://prove2.me/theorems/9d57817b-d4f4-45dd-8431-1afee48a6e2b
-- title:
--   Eqs. (58)-(68): right-hand and left-hand Stokes vectors differ by $T$
-- statement:
--   Let a polarization ellipse have orientation angle $\psi$ and ellipticity angle $\chi$ in the right-hand frame, and let $\psi',\chi'$ be its angles in the left-hand frame. Let $\mathbf I$ and $\mathbf I'$ be the Stokes vectors given by Eq. (1).
--
--   (a) For the definition with $\psi'=\pi/2-\psi$ and $\tan\chi'=1/\tan\chi$ (Eq. 58), with $\tan\chi\ne0$: $\cos2\chi'=-\cos2\chi$ and $\sin2\chi'=\sin2\chi$ (Eqs. 60-61), and
--
--   $$\mathbf I'=(I,Q,-U,V)=T\,\mathbf I,\qquad T=\operatorname{diag}(1,1,-1,1)\quad\text{(Eqs. 63-64)}.$$
--
--   (b) For the definition with $\psi'=\pi-\psi$ and $\tan\chi'=\tan\chi$ (Eq. 65), with $\cos\chi,\cos\chi'\ne0$, the same transformation holds: $\mathbf I'=T\mathbf I$ (Eqs. 66-68).
--
--   (c) $T^2=1$, so the inverse transform is $\mathbf I=T\mathbf I'$.
--
--   **Formalization Note** The hypotheses $\tan\chi\neq0$ and $\cos\chi,\cos\chi'\neq0$ make $\tan\chi$, $\tan\chi'$ and $1/\tan\chi$ finite, as Eqs. (58)-(59) require.
-- source:
--   Zhao, Tan and Liu, On the Derivation of Vector Radiative Transfer Equation for Polarized Radiative Transport in Graded Index Media, arXiv:1110.5134v1 (2011), claim c021; Appendix A, Eqs. (58)-(68), PDF pp. 24-26

import Mathlib
import Definitions.Def_Arxiv1110_5134_Basic

open MeasureTheory Filter Topology
open scoped Matrix

namespace Arxiv1110_5134

theorem stokes_right_to_left_hand (I χ ψ χ' : ℝ) :
    (Real.tan χ ≠ 0 → Real.tan χ' = 1 / Real.tan χ →
      Real.cos (2 * χ') = -Real.cos (2 * χ) ∧ Real.sin (2 * χ') = Real.sin (2 * χ) ∧
      stokesVec I χ' (Real.pi / 2 - ψ) = handT *ᵥ stokesVec I χ ψ) ∧
    (Real.cos χ ≠ 0 → Real.cos χ' ≠ 0 → Real.tan χ' = Real.tan χ →
      stokesVec I χ' (Real.pi - ψ) = handT *ᵥ stokesVec I χ ψ) ∧
    handT * handT = 1 := by sorry

end Arxiv1110_5134

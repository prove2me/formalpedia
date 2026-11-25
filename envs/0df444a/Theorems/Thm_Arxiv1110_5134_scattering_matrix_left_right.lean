-- Prove2me | Theorems.Thm_Arxiv1110_5134_scattering_matrix_left_right
-- name    : Arxiv1110_5134.scattering_matrix_left_right
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-24T09:09:10.246975+00:00
-- url     : https://prove2.me/theorems/822d5f04-3cf7-45e4-b4d9-8fbf9012c564
-- title:
--   Eqs. (69)-(70): scattering matrices in the left-hand and right-hand frames
-- statement:
--   Let $P_{LF}$ be a scattering matrix acting on Stokes vectors defined in the left-hand frame, and $T=\operatorname{diag}(1,1,-1,1)$. A matrix $P$ maps every right-hand incident Stokes vector $\mathbf v$ to the right-hand form $T\,P_{LF}\,T\mathbf v$ of the scattered vector if and only if (Eq. 69)
--
--   $$P=T\,P_{LF}\,T,$$
--
--   and this holds if and only if (Eq. 70)
--
--   $$P_{LF}=T\,P\,T.$$
-- source:
--   Zhao, Tan and Liu, On the Derivation of Vector Radiative Transfer Equation for Polarized Radiative Transport in Graded Index Media, arXiv:1110.5134v1 (2011), claim c023; Appendix A, Eqs. (69)-(70), PDF p. 26

import Mathlib
import Definitions.Def_Arxiv1110_5134_Basic

open MeasureTheory Filter Topology
open scoped Matrix

namespace Arxiv1110_5134

theorem scattering_matrix_left_right (P PLF : Matrix (Fin 4) (Fin 4) ℝ) :
    ((∀ v : Stokes, P *ᵥ v = handT *ᵥ (PLF *ᵥ (handT *ᵥ v))) ↔ P = handT * PLF * handT) ∧
    (P = handT * PLF * handT ↔ PLF = handT * P * handT) := by sorry

end Arxiv1110_5134

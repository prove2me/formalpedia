-- Prove2me | Theorems.Thm_Arxiv1110_5134_phase_matrix_left_hand
-- name    : Arxiv1110_5134.phase_matrix_left_hand
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T09:11:57.506804+00:00
-- url     : https://prove2.me/theorems/55d5a644-3f44-4b72-832c-a3ca0ba215e0
-- title:
--   Eq. (25): the phase matrix from a left-hand-frame scattering matrix
-- statement:
--   If the scattering matrix $P_{LF}$ is given for Stokes vectors defined in a left-hand frame, then substituting $P=T P_{LF}T$ (Eq. 69) into Eq. (22) gives the phase matrix of Eq. (25), and its two printed forms agree:
--
--   $$\Re(\phi-\pi)\,T\,P_{LF}\,T\,\Re(\phi')=\Re(\phi)\,T\,P_{LF}\,T\,\Re(\phi').$$
--
--   **Formalization Note** The statement takes Eq. (22) as the definition of the phase matrix; see the note on Eqs. (22)-(23).
-- source:
--   Zhao, Tan and Liu, On the Derivation of Vector Radiative Transfer Equation for Polarized Radiative Transport in Graded Index Media, arXiv:1110.5134v1 (2011), claim c010; Section 3.2, Eq. (25), PDF p. 14

import Mathlib
import Definitions.Def_Arxiv1110_5134_Basic

open MeasureTheory Filter Topology
open scoped Matrix

namespace Arxiv1110_5134

theorem phase_matrix_left_hand (PLF : Matrix (Fin 4) (Fin 4) ℝ) (φ φ' : ℝ) :
    stokesRot (φ - Real.pi) * (handT * PLF * handT) * stokesRot φ' =
      stokesRot φ * handT * PLF * handT * stokesRot φ' := by sorry

end Arxiv1110_5134

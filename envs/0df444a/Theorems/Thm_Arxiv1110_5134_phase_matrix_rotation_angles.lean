-- Prove2me | Theorems.Thm_Arxiv1110_5134_phase_matrix_rotation_angles
-- name    : Arxiv1110_5134.phase_matrix_rotation_angles
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T09:10:32.434154+00:00
-- url     : https://prove2.me/theorems/a4352992-afa4-4887-9cfd-6455546ba8f5
-- title:
--   Eqs. (22)-(23): the two forms of the phase matrix, and $\cos\phi$, $\cos\phi'$ determine it
-- statement:
--   Let $P$ be a scattering matrix and $\phi,\phi'\in[0,\pi]$. Then the two forms of the scattering phase matrix in Eq. (22) agree,
--
--   $$\Re(\phi-\pi)\,P\,\Re(\phi')=\Re(\phi)\,P\,\Re(\phi'),$$
--
--   and, since $\cos2\phi=2\cos^2\phi-1$ and $\sin2\phi=2\sin\phi\cos\phi$ with $\sin\phi=\sqrt{1-\cos^2\phi}$ on $[0,\pi]$, the matrix $\Re(\phi)P\Re(\phi')$ is determined by $\cos\phi$ and $\cos\phi'$ alone.
--
--   **Formalization Note** Only these two algebraic assertions of Eqs. (22)-(23) are stated. The geometric claim, that the rotations by $\phi'$ and $\phi$ (Eq. 24) carry the Frenet frames of the incident and scattered rays to the scattering plane, is not stated: the orientation of these angles is defined only through Fig. 4.
-- source:
--   Zhao, Tan and Liu, On the Derivation of Vector Radiative Transfer Equation for Polarized Radiative Transport in Graded Index Media, arXiv:1110.5134v1 (2011), claim c009; Section 3.2, Eqs. (22)-(23) and the text after Eq. (23), PDF p. 13

import Mathlib
import Definitions.Def_Arxiv1110_5134_Basic

open MeasureTheory Filter Topology
open scoped Matrix

namespace Arxiv1110_5134

theorem phase_matrix_rotation_angles (P : Matrix (Fin 4) (Fin 4) ℝ) (φ φ' : ℝ)
    (hφ : φ ∈ Set.Icc 0 Real.pi) (hφ' : φ' ∈ Set.Icc 0 Real.pi) :
    stokesRot (φ - Real.pi) * P * stokesRot φ' = stokesRot φ * P * stokesRot φ' ∧
    stokesRot φ * P * stokesRot φ' =
      stokesRotOfCos (Real.cos φ) * P * stokesRotOfCos (Real.cos φ') := by sorry

end Arxiv1110_5134

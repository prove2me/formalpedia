-- Prove2me | Theorems.Thm_Arxiv2602_07094_pauli_moduli_not_amplitude_determined
-- name    : Arxiv2602_07094.pauli_moduli_not_amplitude_determined
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T18:38:52.9558+00:00
-- url     : https://prove2.me/theorems/442720b9-30db-56ff-b45b-089c577b9382
-- title:
--   Section 4: the Pauli moduli |alpha|, |beta| are not functions of the channel amplitudes
-- statement:
--   Neither Pauli modulus is a function of the channel amplitudes on reciprocal Sinclair matrices:
--
--   1. there is no function $F$ of the amplitude matrix $(|S_{ij}|)_{i,j}$ such that $|\alpha(\mathbf S)|=F\big((|S_{ij}|)\big)$ for every reciprocal $\mathbf S$;
--   2. there is no such function for $|\beta(\mathbf S)|$.
--
--   Equivalently, two reciprocal Sinclair matrices can have the same channel amplitudes and different values of $|\alpha|$, and likewise for $|\beta|$. An amplitude-only model therefore cannot reproduce the Pauli image in general.
-- source:
--   Gabot, Frontera-Pons, Fix, Ren and Ovarlez, Exploring Polarimetric properties preservation for PolSAR image reconstruction with Complex-valued Convolutional Neural Networks, arXiv:2602.07094v1 (2026), claim c024; Section 4, opening paragraph, PDF p. 10, with Section 3.1, eq. (4), PDF p. 4

import Mathlib
import Definitions.Def_Arxiv2602_07094_Basic

open Matrix

namespace Arxiv2602_07094

theorem pauli_moduli_not_amplitude_determined :
    (¬ ∃ F : Matrix (Fin 2) (Fin 2) ℝ → ℝ, ∀ S : SinclairMatrix, IsReciprocal S →
        ‖pauliAlpha S‖ = F (channelAmplitudes S)) ∧
    (¬ ∃ F : Matrix (Fin 2) (Fin 2) ℝ → ℝ, ∀ S : SinclairMatrix, IsReciprocal S →
        ‖pauliBeta S‖ = F (channelAmplitudes S)) := by sorry

end Arxiv2602_07094

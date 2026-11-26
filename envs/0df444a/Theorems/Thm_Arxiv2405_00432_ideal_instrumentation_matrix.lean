-- Prove2me | Theorems.Thm_Arxiv2405_00432_ideal_instrumentation_matrix
-- name    : Arxiv2405_00432.ideal_instrumentation_matrix
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-26T12:52:01.598651+00:00
-- url     : https://prove2.me/theorems/5c6e29bd-8d16-4cb6-84a9-99ba7ed1eff0
-- title:
--   Eq. (3)-(4): the ideal instrumentation matrix maps Stokes vectors to POVM intensities
-- statement:
--   Let $\hat\pi_i=\tfrac12|\phi_i\rangle\langle\phi_i|$, $i=1,\dots,4$, be the POVM built from the tetrahedral states of eq. (1), and let $\Pi$ be the ideal instrumentation matrix of eq. (4). Then:
--
--   1. Row $i$ of $\Pi$ is one quarter of the Stokes vector of $|\phi_i\rangle$: $\Pi_{ij}=\tfrac14S_j(\phi_i)$.
--   2. For every nonzero polarization state $\psi\in\mathbb{C}^2$, the normalized intensity vector of the four POVM outcomes and the normalized Stokes vector of $\psi$ satisfy
--   $$I^{(N)}(\psi)=\Pi\,S^{(N)}(\psi).$$
--   3. $\Pi$ is invertible, so $S^{(N)}=\Pi^{-1}I^{(N)}$ recovers the Stokes vector from the four intensities.
--
--   This is the relation on which the single-shot Stokes tomography of the paper rests.
--
--   **Formalization Note** The sign convention $S_3=2\,\mathrm{Im}(E_h\overline{E_v})$ is fixed so that item 1, which the paper asserts, holds; with the opposite sign the third and fourth rows of eq. (4) would have the wrong sign in the last column. The intensity of outcome $i$ is identified with $P_i=\langle\psi|\hat\pi_i|\psi\rangle$, as the paper does for classical light. The invertibility of $\Pi$ is stated as $\det\Pi\neq0$.
-- source:
--   McWilliam, Al Khafaji, Svensson, Pádua and Franke-Arnold, Dynamic Mueller matrix polarimetry using generalized measurements, arXiv:2405.00432v1 (2024), claim c001; Section 2.1, eqs. (1)-(4), PDF p. 3

import Mathlib
import Definitions.Def_Arxiv2405_00432_Basic

open Matrix

namespace Arxiv2405_00432

theorem ideal_instrumentation_matrix :
    (∀ i j : Fin 4, instrMatrix i j = stokes (povmState i) j / 4) ∧
    (∀ ψ : Jones, ψ ≠ 0 → normIntensity ψ = instrMatrix *ᵥ normStokes ψ) ∧
    IsUnit instrMatrix.det := by sorry

end Arxiv2405_00432

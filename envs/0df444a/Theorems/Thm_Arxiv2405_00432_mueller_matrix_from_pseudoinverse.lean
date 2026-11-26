-- Prove2me | Theorems.Thm_Arxiv2405_00432_mueller_matrix_from_pseudoinverse
-- name    : Arxiv2405_00432.mueller_matrix_from_pseudoinverse
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-26T12:54:12.022185+00:00
-- url     : https://prove2.me/theorems/e0dc51ca-9d82-5853-af2b-c02513106913
-- title:
--   Eqs. (5)-(7): the Mueller matrix from a Poincaré beam via the right pseudo-inverse
-- statement:
--   Let $\mathcal S_{\rm in}$ and $\mathcal S_{\rm out}$ be real $4\times N$ matrices whose $n$-th columns are the Stokes vectors of the probe beam at pixel $n$ before and after a homogeneous sample with real $4\times4$ Mueller matrix $M$, so that
--   $$\mathcal S_{\rm out}=M\,\mathcal S_{\rm in}.$$
--   Then:
--
--   1. $\mathcal S_{\rm in}\mathcal S_{\rm in}^T$ is invertible if and only if the beam profile contains four linearly independent polarization states, that is, four columns of $\mathcal S_{\rm in}$ are linearly independent.
--   2. In that case the right Moore-Penrose pseudo-inverse $\mathcal S_{\rm in}^\dagger=\mathcal S_{\rm in}^T[\mathcal S_{\rm in}\mathcal S_{\rm in}^T]^{-1}$ satisfies $\mathcal S_{\rm in}\mathcal S_{\rm in}^\dagger=I_4$, and
--   $$M=\mathcal S_{\rm out}\,\mathcal S_{\rm in}^\dagger.$$
--
--   This is the reconstruction step of single-shot Mueller matrix polarimetry with a Poincaré beam.
--
--   **Formalization Note** The paper's remark that the method works only if the beam contains four linearly independent polarization states is stated as item 1. The columns are arbitrary real vectors: the measured Stokes vectors are not assumed to satisfy $S_0^2\ge S_1^2+S_2^2+S_3^2$, since the paper applies eq. (7) to measured data.
-- source:
--   McWilliam, Al Khafaji, Svensson, Pádua and Franke-Arnold, Dynamic Mueller matrix polarimetry using generalized measurements, arXiv:2405.00432v1 (2024), claim c002; Section 2.2, eqs. (5), (6), (7) and the sentence after eq. (7), PDF p. 4

import Mathlib
import Definitions.Def_Arxiv2405_00432_Basic

open Matrix

namespace Arxiv2405_00432

theorem mueller_matrix_from_pseudoinverse {N : ℕ} (M : Matrix (Fin 4) (Fin 4) ℝ)
    (Sin Sout : Matrix (Fin 4) (Fin N) ℝ) (hlin : Sout = M * Sin) :
    (IsUnit (Sin * Sinᵀ).det ↔ HasFourIndependentStates Sin) ∧
    (HasFourIndependentStates Sin →
      Sin * rightPseudoInv Sin = 1 ∧ M = Sout * rightPseudoInv Sin) := by sorry

end Arxiv2405_00432

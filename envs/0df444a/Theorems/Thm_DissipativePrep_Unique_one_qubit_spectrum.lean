-- Prove2me | Theorems.Thm_DissipativePrep_Unique_one_qubit_spectrum
-- name    : DissipativePrep.Unique.one_qubit_spectrum
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:47:06.53257+00:00
-- url     : https://prove2.me/theorems/3059fe1e-4c8d-4a1f-a341-f2d4a3e315b5
-- title:
--   §IV.A, p. 4 — one qubit: eigenvalues 0, −2g, −g, −g of L_{σ₋} on |0⟩⟨0|, σ_z, σ_x, σ_y
-- statement:
--   Consider a single qubit with Hamiltonian $0$ and one jump operator $\sigma_- = |0\rangle\langle 1| = \begin{pmatrix}0&1\\0&0\end{pmatrix}$ with rate $g>0$, so that $\mathcal L(\rho) = g\,(2\sigma_-\rho\sigma_-^\dagger - \sigma_-^\dagger\sigma_-\rho - \rho\sigma_-^\dagger\sigma_-)$. Then
--   $$\mathcal L(|0\rangle\langle0|) = 0,\qquad \mathcal L(\sigma_z) = -2g\,\sigma_z,\qquad \mathcal L(\sigma_x) = -g\,\sigma_x,\qquad \mathcal L(\sigma_y) = -g\,\sigma_y,$$
--   where $\sigma_z = \begin{pmatrix}1&0\\0&-1\end{pmatrix}$, $\sigma_x = \begin{pmatrix}0&1\\1&0\end{pmatrix}$, $\sigma_y = \begin{pmatrix}0&-i\\i&0\end{pmatrix}$ (basis order $|0\rangle,|1\rangle$).
--
--   These four eigenvectors form a basis of the $2\times2$ matrices, so they give the full spectrum $\lambda_0 = 0$, $\lambda_3 = -2g$, $\lambda_1 = \lambda_2 = -g$ of the single-qubit Liouvillian; the $n$-qubit spectrum is built from them.
--
--   **Formalization Note** The page says "$\mathcal L(\sigma_i) = \lambda_i\sigma_i$ iff $\sigma_i\in\Sigma_k$"; read literally the "iff" is false (e.g. $2\sigma_z$ is an eigenvector outside $\Sigma_k$), so the four eigen-equations are stated.
-- source:
--   Kraus et al., Preparation of entangled states by quantum Markov processes, arXiv:0803.1463v3, p. 4, §IV.A ("We find L_{σ_-^{(k)}}(σ_i^{(k)}) = λ_iσ_i^{(k)} …")

import Mathlib
import Definitions.Def_DissipativePrep_Unique_Model

open scoped Matrix ComplexConjugate
open QAlgorithms QAlgorithms.Papers.Independent.Dependency50.P16

namespace DissipativePrep.Unique

theorem one_qubit_spectrum (g : ℝ) (hg : 0 < g) :
    let G := gkslGenerator (krausData (0 : Matrix (Fin 2) (Fin 2) ℂ) Matrix.isHermitian_zero
      ![!![0, 1; 0, 0]] ![g])
    G !![1, 0; 0, 0] = 0 ∧
    G !![1, 0; 0, -1] = ((-2 * g : ℝ) : ℂ) • !![1, 0; 0, -1] ∧
    G !![0, 1; 1, 0] = ((-g : ℝ) : ℂ) • !![0, 1; 1, 0] ∧
    G !![0, -Complex.I; Complex.I, 0] = ((-g : ℝ) : ℂ) • !![0, -Complex.I; Complex.I, 0] := by sorry

end DissipativePrep.Unique

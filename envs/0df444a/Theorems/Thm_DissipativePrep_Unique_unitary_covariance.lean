-- Prove2me | Theorems.Thm_DissipativePrep_Unique_unitary_covariance
-- name    : DissipativePrep.Unique.unitary_covariance
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:47:08.779127+00:00
-- url     : https://prove2.me/theorems/a6f8f268-c886-4c53-a48d-0838c798cf0a
-- title:
--   §IV.A, p. 4 — L_{Uσ₋U†}(σ) = U L_{σ₋}(U†σU) U†, and the eigen-equations correspond
-- statement:
--   Let $U$ be a unitary on $n$ qubits and $g_1,\dots,g_n>0$. Write $\mathcal L_{\{c_k\}}$ for the purely dissipative Liouvillian of Eq. (2) with jump operators $c_k = U\sigma_-^{(k)}U^\dagger$ and rates $g_k$, and $\mathcal L_{\{\sigma_-^{(k)}\}}$ for the one with jump operators $\sigma_-^{(k)}$ and the same rates. Then for every operator $\sigma$
--   $$\mathcal L_{\{U\sigma_-^{(k)}U^\dagger\}}(\sigma) = U\,\mathcal L_{\{\sigma_-^{(k)}\}}(U^\dagger\sigma U)\,U^\dagger,$$
--   and consequently, for every $\lambda\in\mathbb C$,
--   $$\mathcal L_{\{U\sigma_-^{(k)}U^\dagger\}}(\sigma) = \lambda\sigma \iff \mathcal L_{\{\sigma_-^{(k)}\}}(U^\dagger\sigma U) = \lambda\,U^\dagger\sigma U.$$
--
--   This reduces the spectral analysis of the process for an arbitrary target state to the case $U = \mathbb 1$.
--
--   **Formalization Note** "Purely dissipative" means $H = 0$. Rates $g_k>0$ are assumed throughout the mission.
-- source:
--   Kraus et al., Preparation of entangled states by quantum Markov processes, arXiv:0803.1463v3, p. 4, §IV.A

import Mathlib
import Definitions.Def_DissipativePrep_Unique_Model

open scoped Matrix ComplexConjugate
open QAlgorithms QAlgorithms.Papers.Independent.Dependency50.P16

namespace DissipativePrep.Unique

theorem unitary_covariance {n : ℕ} (U : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) (g : Fin n → ℝ) (hg : ∀ k, 0 < g k) :
    (∀ σ : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ,
      gkslGenerator (prepData U g 0 Matrix.isHermitian_zero) σ =
        U * gkslGenerator (prepData 1 g 0 Matrix.isHermitian_zero) (Uᴴ * σ * U) * Uᴴ) ∧
    ∀ (σ : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) (μ : ℂ),
      gkslGenerator (prepData U g 0 Matrix.isHermitian_zero) σ = μ • σ ↔
        gkslGenerator (prepData 1 g 0 Matrix.isHermitian_zero) (Uᴴ * σ * U) = μ • (Uᴴ * σ * U) := by sorry

end DissipativePrep.Unique

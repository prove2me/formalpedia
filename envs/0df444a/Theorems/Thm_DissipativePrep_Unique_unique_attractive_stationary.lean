-- Prove2me | Theorems.Thm_DissipativePrep_Unique_unique_attractive_stationary
-- name    : DissipativePrep.Unique.unique_attractive_stationary
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:47:16.990752+00:00
-- url     : https://prove2.me/theorems/9790b7b6-dc3e-4184-9934-4a6b30c69c98
-- title:
--   §IV and §IV.A, p. 4 — U|0ⁿ⟩ is the unique stationary state of L_{H,c_k}, c_k = Uσ₋^{(k)}U†; for H = 0 it attracts every state and T_relax = 1/min_k g_k
-- statement:
--   Let $n\ge 1$, let $U$ be a unitary on $n$ qubits, $|\Psi\rangle = U|0^n\rangle$, and $c_k = U\sigma_-^{(k)}U^\dagger$ for $k = 1,\dots,n$, where $\sigma_-^{(k)} = \mathbb 1\otimes\dots\otimes|0\rangle_k\langle1|\otimes\dots\otimes\mathbb 1$. Let $g_1,\dots,g_n>0$ and $g_{\min} = \min_k g_k$. Then:
--
--   1. **Uniqueness.** For every Hermitian $H$ having $|\Psi\rangle$ as an eigenvector ($H|\Psi\rangle = E|\Psi\rangle$, $E\in\mathbb R$), the only stationary state of $\mathcal L_{H,c_k}$ is $|\Psi\rangle\langle\Psi|$: a density matrix $\rho$ satisfies $\mathcal L_{H,c_k}(\rho) = 0$ if and only if $\rho = |\Psi\rangle\langle\Psi|$.
--   2. **Preparation.** For the purely dissipative process ($H = 0$), every initial density matrix converges to the target:
--   $$e^{t\mathcal L_{\{c_k\}}}(\rho) \xrightarrow[t\to\infty]{} |\Psi\rangle\langle\Psi| \quad\text{for every density matrix } \rho.$$
--   3. **Relaxation time.** For $H = 0$, the least value of $-\operatorname{Re}\mu$ over the nonzero eigenvalues $\mu$ of $\mathcal L_{\{c_k\}}$ is $g_{\min}$; equivalently the relaxation time is
--   $$T_{\mathrm{relax}} = \frac{1}{\min_k g_k}.$$
--
--   Every pure state of $n$ qubits is thus the unique and attractive stationary state of a dissipative process whose relaxation time does not depend on $n$.
--
--   **Formalization Note** Three hypotheses are added relative to the page: $g_k>0$ (the page allows $g_\ell\ge 0$; with $g_k = 0$ uniqueness fails and $T_{\mathrm{relax}} = \infty$), $n\ge 1$ (for $n = 0$ there is no nonzero eigenvalue and $\min_k g_k$ is undefined), and $g_{\min}$ is given as the least element of $\{g_1,\dots,g_n\}$. Convergence is in the entrywise topology on matrices; the semigroup is the matrix exponential of the Liouvillian.
-- source:
--   Kraus et al., Preparation of entangled states by quantum Markov processes, arXiv:0803.1463v3, p. 4, §IV ("This immediately implies …") and §IV.A (Eq. (5); "We find T_relax = 1/min_k g_k"), with Eq. (1), p. 1

import Mathlib
import Definitions.Def_DissipativePrep_Unique_Model

open scoped Matrix ComplexConjugate
open QAlgorithms QAlgorithms.Papers.Independent.Dependency50.P16

namespace DissipativePrep.Unique

theorem unique_attractive_stationary {n : ℕ} (hn : 1 ≤ n)
    (U : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ)
    (g : Fin n → ℝ) (hg : ∀ k, 0 < g k) (gmin : ℝ) (hgmin : IsLeast (Set.range g) gmin) :
    (∀ (H : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) (hH : H.IsHermitian) (E : ℝ),
        act H (target U) = (E : ℂ) • target U →
        ∀ ρ, stationary (prepData U g H hH) ρ ↔ ρ = pureDensity (target U)) ∧
    attractive (prepData U g 0 Matrix.isHermitian_zero) (pureDensity (target U)) ∧
    IsLeast (relaxRates (gkslGenerator (prepData U g 0 Matrix.isHermitian_zero))) gmin ∧
    IsRelaxTime (gkslGenerator (prepData U g 0 Matrix.isHermitian_zero)) (1 / gmin) := by sorry

end DissipativePrep.Unique

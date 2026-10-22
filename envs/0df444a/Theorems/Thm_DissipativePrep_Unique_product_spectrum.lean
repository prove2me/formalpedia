-- Prove2me | Theorems.Thm_DissipativePrep_Unique_product_spectrum
-- name    : DissipativePrep.Unique.product_spectrum
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:47:14.097713+00:00
-- url     : https://prove2.me/theorems/6b71d71a-7fd2-40c2-97da-d7d6effc9335
-- title:
--   §IV.A, p. 4 — explicit tensor eigenbasis of L_{c_k} with eigenvalues −Σ_k m_k g_k, m_k ∈ {0,1,2}
-- statement:
--   Let $U$ be a unitary on $n$ qubits, $g_1,\dots,g_n>0$, and let $\mathcal L = \mathcal L_{\{c_k\}}$ be the purely dissipative Liouvillian of Eq. (2) with jump operators $c_k = U\sigma_-^{(k)}U^\dagger$ and rates $g_k$, acting on $2^n\times 2^n$ complex matrices. Then
--
--   1. the eigenvalues of $\mathcal L$ are exactly the numbers
--   $$\lambda_{i_1,\dots,i_n} = \sum_k \lambda_{i_k} = -\sum_{k=1}^n m_k\,g_k,\qquad m_k\in\{0,1,2\},$$
--   where $m_k = 0,1,2$ corresponds to $\lambda_0 = 0$, $\lambda_1 = \lambda_2 = -g_k$, $\lambda_3 = -2g_k$;
--   2. the explicit operators $U(\sigma_{i_1}^{(1)}\otimes\cdots\otimes\sigma_{i_n}^{(n)})U^\dagger$, with $i_k\in\{0,1,2,3\}$, form a basis, and each has eigenvalue $\sum_k\lambda_{i_k}$.
--
--   This is the complete solution of the master equation $\dot\rho = \mathcal L(\rho)$ for the constructed process, from which convergence and the relaxation time are read off.
--
--   **Formalization Note** The tensor product is given entrywise on Boolean bit strings and transported to $\{0,\dots,2^n-1\}$. The statement records the eigen-equation for every indexed tensor product, their linear independence and span, and the exact eigenvalue set. Rates $g_k>0$ are assumed.
-- source:
--   Kraus et al., Preparation of entangled states by quantum Markov processes, arXiv:0803.1463v3, p. 4, §IV.A ("Thus, a basis of the eigenvectors of the total Liouvillian …")

import Mathlib
import Definitions.Def_DissipativePrep_Unique_Model

open scoped Matrix ComplexConjugate
open QAlgorithms QAlgorithms.Papers.Independent.Dependency50.P16

namespace DissipativePrep.Unique

theorem product_spectrum {n : ℕ} (U : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) (g : Fin n → ℝ) (hg : ∀ k, 0 < g k) :
    let G := gkslGenerator (prepData U g 0 Matrix.isHermitian_zero)
    let σ := fun i : Fin n → Fin 4 => U * tensorEigenoperator i * Uᴴ
    (∀ i, G (σ i) = (∑ k, localEigenvalue (g k) (i k)) • σ i) ∧
    LinearIndependent ℂ σ ∧
    Submodule.span ℂ (Set.range σ) = ⊤ ∧
    (∀ μ : ℂ, G.HasEigenvalue μ ↔
      ∃ m : Fin n → Fin 3, μ = -(∑ k, ((m k : ℕ) : ℂ) * (g k : ℂ))) := by sorry

end DissipativePrep.Unique

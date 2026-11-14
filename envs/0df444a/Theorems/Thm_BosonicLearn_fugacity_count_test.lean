-- Prove2me | Theorems.Thm_BosonicLearn_fugacity_count_test
-- name    : BosonicLearn.fugacity_count_test
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-13T19:56:28.728823+00:00
-- url     : https://prove2.me/theorems/5abe194a-0f01-4b20-a511-627fca340d0c
-- title:
--   Data processing for a thresholded photon count: $|\Pr_{\rho_{R_2}}(K>\tau)-\Pr_{\rho_{R_1}}(K>\tau)|\le\|\rho_{R_2}-\rho_{R_1}\|_1$
-- statement:
--   Data processing for the two-outcome measurement "rotate by a passive unitary, count the photons in a set of modes, compare with a threshold".
--
--   Let $R_1,R_2$ be fugacity matrices (positive semidefinite with $1-R_i$ positive definite), $\rho_{R}=\det(1-R)\Gamma(R)$, $U$ a unitary $n\times n$ matrix, $A$ a set of modes and $\tau\in\mathbb N$. Let $p^{(i)}_k=\sum_{w:\sum_{j\in A}w_j=k}\langle w|\rho_{UR_iU^\dagger}|w\rangle$ be the law of the photon count $K$ in the modes $A$ after the passive unitary of $U$. Then
--
--   $$
--   \Big|\sum_{k>\tau}p^{(2)}_k-\sum_{k>\tau}p^{(1)}_k\Big|\le\big\|\rho_{R_2}-\rho_{R_1}\big\|_1 .
--   $$
--
--   Role. Last step of the proof of Lemma 12 (Eqs. (147)–(148)): a gap between the two tail probabilities of the photon count lower-bounds the trace distance of the two states.
--
--   **Formalization Note** The right-hand side is the full trace norm `traceSize` (without the factor $\tfrac12$ of the trace distance; the constant is immaterial for Lemma 12). $\rho_R$ is `fugacityCoeff R`; the rotated state is written `fugacityCoeff (U * R * Uᴴ)`, which is $\Gamma(U)\rho_R\Gamma(U)^\dagger$.
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, §5.7 (Delayed proof for Lemma 12), proof of Lemma 12, Eqs. (147)–(148) (coarse-graining of the photon count and data processing)

import Mathlib
import Definitions.Def_BosonicLearn_fugacityCoeff
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33

open QAlgorithms.Papers.Independent.Dependency50.P33 (traceSize)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open scoped ENNReal Matrix ComplexOrder

namespace BosonicLearn

/-- **Data processing for a thresholded photon count.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, §5.7, proof of Lemma 12, Eqs. (147)–(148): "Coarse-graining the photon count into the two outcomes {K̂ > τ} and {K̂ ≤ τ}
gives a classical total variation distance equal to the absolute value of the left-hand side of Eq. (147). By data
processing for trace distance …".

Let `R₁, R₂` be fugacity matrices (positive semidefinite, `1 − R_i` positive definite), `U` a unitary matrix, `A` a set
of modes and `τ` a threshold. For `i = 1, 2` let `p^{(i)}_k = ∑_{w : ∑_{j∈A} w_j = k} ⟨w|ρ_{U R_i U†}|w⟩` be the law of the
photon count in the modes `A` after the passive unitary of `U`. Then

`|∑_{k > τ} p^{(2)}_k − ∑_{k > τ} p^{(1)}_k| ≤ ‖ρ_{R₂} − ρ_{R₁}‖₁`.

**Formalization Note.** The right-hand side is the full trace norm `traceSize` (no factor `½`); the constant is
irrelevant for Lemma 12. `ρ_R` is `fugacityCoeff R`. -/
theorem fugacity_count_test {n : ℕ} (R₁ R₂ : Matrix (Fin n) (Fin n) ℂ) (h₁ : R₁.PosSemidef)
    (h₁' : (1 - R₁).PosDef) (h₂ : R₂.PosSemidef) (h₂' : (1 - R₂).PosDef)
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : Uᴴ * U = 1) (A : Finset (Fin n)) (τ : ℕ) :
    ENNReal.ofReal |(∑' k : ℕ, if τ < k then (∑' w : Occupation (Fin n),
          if ∑ i ∈ A, w i = k then (fugacityCoeff (U * R₂ * Uᴴ) w w).re else 0) else 0) -
        ∑' k : ℕ, if τ < k then (∑' w : Occupation (Fin n),
          if ∑ i ∈ A, w i = k then (fugacityCoeff (U * R₁ * Uᴴ) w w).re else 0) else 0| ≤
      traceSize (fugacityCoeff R₂ - fugacityCoeff R₁) := by sorry

end BosonicLearn

-- Prove2me | Theorems.Thm_BosonicLearn_occupation_count_separation
-- name    : BosonicLearn.occupation_count_separation
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-14T02:11:00.643002+00:00
-- url     : https://prove2.me/theorems/74635198-2a3b-429a-8991-d270eb07202a
-- title:
--   Trace-norm separation of passive Gaussian states from their occupation matrices, uniform in temperature: $\|\rho_1-\rho_2\|_1\ge c\,\mathrm{Tr}(N_1-N_2)^2/(\theta m^2\sqrt n)$
-- statement:
--   The pairwise-distance bound for the hard ensemble of Theorem 9, by the photon-counting argument of Lemma 12, with a constant independent of the temperature scale $m$.
--
--   There is an absolute constant $c>0$ such that: for $m\ge1$, $\theta>0$ with $\theta\sqrt n\le\frac78$, and Hermitian $n\times n$ occupation matrices $N_1,N_2$ with $\frac78m\,\mathbf 1\preceq N_i\preceq\frac98m\,\mathbf 1$, $\operatorname{Tr}(N_1-N_2)=0$ and $-\theta m\,\mathbf 1\preceq N_1-N_2\preceq\theta m\,\mathbf 1$, the passive Gaussian states $\rho_i=\det(\mathbf 1-R_i)\Gamma(R_i)$ with fugacity matrices $R_i=N_i(\mathbf 1+N_i)^{-1}$ satisfy
--
--   $$\|\rho_1-\rho_2\|_1\ \ge\ c\,\frac{\operatorname{Tr}(N_1-N_2)^2}{\theta\,m^2\sqrt n}.$$
--
--   With $N_i=m(\mathbf 1+\xi X_i)$, $\|X_i\|_{\rm op}\le4$ and $\theta=8\xi$ the right-hand side is $\frac c8\,\xi\,\|X_1-X_2\|_F^2/\sqrt n$.
--
--   Proof idea: count photons in the positive eigen-directions of $N_1-N_2$; the two counts are sums of geometric variables with paired means (`BosonicLearn.loewner_eigenvalue_pairing`, `BosonicLearn.fugacity_count_pgf`), a threshold separates them (`BosonicLearn.geometric_threshold_scaled`), and data processing (`BosonicLearn.fugacity_count_test`) transfers this to the trace norm.
--
--   **Formalization Note** $\|\cdot\|_1$ is the full trace norm `traceSize`; the lower bound is `ENNReal.ofReal (…)`.
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, §8, proof of Theorem 9, pp. 65–67 (Eqs. (226)–(228): pairwise trace distance of the ensemble); §5.7, proof of Lemma 12, Eqs. (135)–(148)

import Mathlib
import Definitions.Def_BosonicLearn_fugacityCoeff
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33

open QAlgorithms.Papers.Independent.Dependency50.P33 (traceSize)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open scoped ENNReal Matrix ComplexOrder

namespace BosonicLearn

/-- **Trace-norm separation of passive Gaussian states from their occupation matrices, uniformly in temperature.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, §8, proof of Theorem 9, Eqs. (226)–(228), p. 66 (pairwise trace distance of the hard ensemble for `ν ≥ 1`), by the
photon-counting argument of §5.7 (proof of Lemma 12, Eqs. (135)–(148)).

There is an absolute constant `c > 0` with the following property. Let `m ≥ 1` and let `N₁, N₂` be Hermitian `n × n`
occupation matrices with `(7/8)m·1 ⪯ N_i ⪯ (9/8)m·1`, `Tr(N₁ − N₂) = 0` and `−θm·1 ⪯ N₁ − N₂ ⪯ θm·1`, where
`θ√n ≤ 7/8`. Then the passive Gaussian states `ρ_i = det(1 − R_i)Γ(R_i)` with fugacity matrices
`R_i = N_i(1 + N_i)⁻¹` satisfy

`‖ρ₁ − ρ₂‖₁ ≥ c · Tr (N₁ − N₂)² / (θ m² √n)`.

**Formalization Note.** `‖·‖₁` is the full trace norm `traceSize`. With `N_i = m(1 + ξX_i)`, `‖X_i‖_op ≤ 4` and
`θ = 8ξ` the right-hand side is `(c/8) ξ ‖X₁ − X₂‖_F² / √n`; the bound does not depend on `m`. -/
theorem occupation_count_separation :
    ∃ c : ℝ, 0 < c ∧ ∀ (n : ℕ) (m θ : ℝ), 1 ≤ m → 0 < θ → θ * Real.sqrt n ≤ 7 / 8 →
      ∀ N₁ N₂ : Matrix (Fin n) (Fin n) ℂ,
        (N₁ - ((7 / 8 * m : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosSemidef →
        (((9 / 8 * m : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - N₁).PosSemidef →
        (N₂ - ((7 / 8 * m : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosSemidef →
        (((9 / 8 * m : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - N₂).PosSemidef →
        (N₁ - N₂).trace = 0 →
        (((θ * m : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - (N₁ - N₂)).PosSemidef →
        (((θ * m : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) + (N₁ - N₂)).PosSemidef →
        ENNReal.ofReal (c * ((N₁ - N₂) * (N₁ - N₂)).trace.re / (θ * m ^ 2 * Real.sqrt n)) ≤
          traceSize (fugacityCoeff (N₁ * (1 + N₁)⁻¹) - fugacityCoeff (N₂ * (1 + N₂)⁻¹)) := by sorry

end BosonicLearn

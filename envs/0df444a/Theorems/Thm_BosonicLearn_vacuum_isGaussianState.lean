-- Prove2me | Theorems.Thm_BosonicLearn_vacuum_isGaussianState
-- name    : BosonicLearn.vacuum_isGaussianState
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-13T18:22:28.270829+00:00
-- url     : https://prove2.me/theorems/e5ad2630-f29f-4a47-abc1-9551e4dcabc1
-- title:
--   The vacuum $|0\rangle\langle0|$ is the Gaussian state $\rho(0,\tfrac12 I)$
-- statement:
--   The $n$-mode vacuum is a Gaussian state with mean $0$ and covariance $\tfrac12\mathbf 1$.
--
--   For every $n$, the operator $|0\rangle\langle 0|$ on the $n$-mode Fock space $\ell^2(\mathbb N^n)$, with coefficient $1$ at $(u,v)=(0,0)$ and $0$ elsewhere in the Fock basis, is a density operator, and it is the Gaussian state $\rho(\mu,\Sigma)$ with
--
--   $$
--   \mu=0,\qquad \Sigma=\tfrac12\,\mathbf 1_{2n}.
--   $$
--
--   Role. (i) It confirms on the simplest example the conventions of the predicate used throughout the mission: quadratures $\hat q=(\hat a+\hat a^\dagger)/\sqrt2$, $\hat p=(\hat a-\hat a^\dagger)/(\mathrm i\sqrt2)$ and $\Sigma_{kl}=\tfrac12\operatorname{Tr}(\rho\{\hat r_k-\mu_k,\hat r_l-\mu_l\})$, so that the vacuum has $\Sigma=\tfrac12\mathbf 1$ and the promise $\Sigma\succeq(\tfrac12+\nu)\mathbf 1$ of Theorem 3 measures the gap above the vacuum. (ii) It shows that Gaussian states exist for every $n$; a default Gaussian state is needed by `BosonicLearn.gaussianState_measurable_family`.
--
--   **Formalization Note** The conclusion is the existence of a `State (Occupation (Fin n))` with the stated coefficients satisfying `IsGaussianState ρ 0 ((1/2) • 1)`. Through `Support50.P14.GaussianAt` this includes the characteristic-function identity $\operatorname{Tr}(\rho\,e^{\mathrm i\xi\cdot\hat r})=\exp(-\tfrac12\xi^\top\Sigma\xi)$ computed with the published displacement matrix elements, finite energy, convergence of the trace series, and the first and second moment identities.
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, §1.1, Eqs. (2) and (4), pp. 4–5 (Gaussian states ρ(µ, Σ)); Theorem 3, p. 6 (vacuum gap ν above ½I)

import Mathlib
import Definitions.Def_BosonicLearn_IsGaussianState

open QAlgorithms.Papers.Independent.Dependency50.P33 (State traceSize)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open scoped ENNReal Matrix

namespace BosonicLearn

/-- **The vacuum is the Gaussian state `ρ(0, ½I)`.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, §1.1, Eqs. (2) and (4), pp. 4–5: "A Gaussian state is a state whose Wigner function is a Gaussian
distribution … thus we denote a Gaussian state by ρ(µ, Σ)"; Theorem 3, p. 6: the promise `Σ ≥ (1/2 + ν)I`
measures the gap above the vacuum covariance `½I`.

For every `n` the `n`-mode vacuum `|0⟩⟨0|` (coefficient `1` at `(0, 0)` and `0` elsewhere in the Fock basis) is a
density operator, and it is the Gaussian state with mean `0` and covariance matrix `½ I`.

**Formalization Note.** This checks the conventions of `IsGaussianState` (grouped quadratures, vacuum covariance
`½I`) on the simplest example, and shows that the set of Gaussian states is non-empty for every `n`. -/
theorem vacuum_isGaussianState (n : ℕ) :
    ∃ ρ : State (Occupation (Fin n)),
      (∀ u v, ρ.coefficients u v = if u = 0 ∧ v = 0 then 1 else 0) ∧
      IsGaussianState ρ 0 ((1 / 2 : ℝ) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)) := by sorry

end BosonicLearn

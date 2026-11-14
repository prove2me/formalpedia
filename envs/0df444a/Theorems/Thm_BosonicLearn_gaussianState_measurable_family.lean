-- Prove2me | Theorems.Thm_BosonicLearn_gaussianState_measurable_family
-- name    : BosonicLearn.gaussianState_measurable_family
-- status  : Open
-- author  : @Senrui Chen
-- created : 2026-11-13T07:03:15.564169+00:00
-- url     : https://prove2.me/theorems/df4b29a4-3f70-41a1-b1fa-cd54e39e284e
-- title:
--   A measurable family of Gaussian states $(\mu,\Sigma)\mapsto\rho(\mu,\Sigma)$
-- statement:
--   Gaussian states can be chosen measurably in their first and second moments.
--
--   For every $n$ there is a map $\mathrm{gs}$ from pairs $(\mu,S)$, $\mu\in\mathbb R^{2n}$, $S\in\mathbb R^{2n\times2n}$, to density operators on the $n$-mode Fock space such that
--
--   1. $\mathrm{gs}$ is measurable, for the Borel sets of $\mathbb R^{2n}\times\mathbb R^{2n\times2n}$ and the Borel sets of the trace-norm topology on density operators;
--   2. every value $\mathrm{gs}(\mu,S)$ is a Gaussian state (with some mean and covariance);
--   3. whenever there exists a Gaussian state with mean $\mu$ and covariance matrix $\Sigma$, the value $\mathrm{gs}(\mu,\Sigma)$ is a Gaussian state with mean $\mu$ and covariance $\Sigma$.
--
--   Why it holds. The pairs $(\mu,\Sigma)$ that are moments of a Gaussian state are those with $\Sigma$ symmetric and $\Sigma+\tfrac{\mathrm i}2\Omega\succeq0$, a closed set; on it $(\mu,\Sigma)\mapsto\rho(\mu,\Sigma)$ is continuous in trace norm (pointwise convergence of characteristic functions of states to that of a state implies trace-norm convergence). Elsewhere take the vacuum.
--
--   Role. The estimator of Theorem 8 outputs $\hat\rho=\rho(\hat\mu,\tilde\Sigma)$, where $\hat\mu,\tilde\Sigma$ are measurable functions of the heterodyne outcomes; the statement of Theorem 8 requires the estimator to be a measurable map into states all of whose values are Gaussian states. This lemma supplies it, including on outcomes for which $\tilde\Sigma$ is not a valid covariance matrix.
--
--   **Formalization Note** `IsGaussianState ρ μ S` is the mission's predicate for $\rho=\rho(\mu,\Sigma)$: the characteristic function of $\rho$ is $\exp(\mathrm i\xi\cdot\mu-\tfrac12\xi^\top\Sigma\xi)$, together with finite energy, symmetry of $\Sigma$ and the first and second moment identities; quadratures are in grouped order $(q_1,\dots,q_n,p_1,\dots,p_n)$ and the vacuum has $\Sigma=\tfrac12\mathbf 1$. States are `State (Occupation (Fin n))`, density operators on $\ell^2(\mathbb N^n)$. The covariance argument of `gs` is a function `Fin n ⊕ Fin n → Fin n ⊕ Fin n → ℝ`, so that the product $\sigma$-algebra of function spaces applies (`Matrix` carries no measurable structure in Mathlib). The source uses the family $\rho(\mu,\Sigma)$ without comment.
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, §1.1, p. 5 (Gaussian states ρ(µ, Σ)); Theorem 8 and Eq. (211), p. 61 (the protocol outputs the valid Gaussian state ρ̂ = ρ(µ̂, Σ̃))

import Mathlib
import Definitions.Def_BosonicLearn_traceDist
import Definitions.Def_BosonicLearn_IsGaussianState

open QAlgorithms.Papers.Independent.Dependency50.P33 (State traceSize)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open MeasureTheory
open scoped ENNReal Matrix

namespace BosonicLearn

/-- **A measurable family of Gaussian states `(µ, Σ) ↦ ρ(µ, Σ)`.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, §1.1, p. 5: "Such a state is completely determined by its first and second moments … thus we denote a
Gaussian state by ρ(µ, Σ)"; Theorem 8, p. 61: "a non-adaptive protocol … that always outputs a valid Gaussian
state ρ̂", with `ρ̂ = ρ(µ̂, Σ̃)` computed from the measurement outcomes (Eq. (211)).

There is a map `gs` from pairs (vector `µ ∈ ℝ²ⁿ`, array `S ∈ ℝ^{2n×2n}`) to density operators on the `n`-mode Fock
space such that
1. `gs` is measurable (Borel sets of `ℝ²ⁿ × ℝ^{2n×2n}`; trace-norm Borel sets of states);
2. every value of `gs` is a Gaussian state;
3. whenever a Gaussian state with mean `µ` and covariance `Σ` exists, `gs (µ, Σ)` is such a state.

**Formalization Note.** The covariance argument is a function `Fin n ⊕ Fin n → Fin n ⊕ Fin n → ℝ` (grouped
quadratures) so that the product σ-algebra of functions is used. On pairs that are not the moments of a
Gaussian state the value is some Gaussian state (for instance the vacuum). Measurability follows from
continuity of `(µ, Σ) ↦ ρ(µ, Σ)` in trace norm on the closed set of valid pairs. -/
theorem gaussianState_measurable_family (n : ℕ) :
    ∃ gs : (Fin n ⊕ Fin n → ℝ) × (Fin n ⊕ Fin n → Fin n ⊕ Fin n → ℝ) → State (Occupation (Fin n)),
      Measurable gs ∧
      (∀ p, ∃ (μ : Fin n ⊕ Fin n → ℝ) (S : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ),
        IsGaussianState (gs p) μ S) ∧
      ∀ (μ : Fin n ⊕ Fin n → ℝ) (S : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)
        (ρ : State (Occupation (Fin n))), IsGaussianState ρ μ S →
        IsGaussianState (gs (μ, fun a b => S a b)) μ S := by sorry

end BosonicLearn

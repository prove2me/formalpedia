-- Prove2me | Theorems.Thm_BosonicLearn_gaussianState_classical_family
-- name    : BosonicLearn.gaussianState_classical_family
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-13T21:08:11.795287+00:00
-- url     : https://prove2.me/theorems/93a58938-1f7b-4ae0-8a20-bba44089424a
-- title:
--   A measurable family of Gaussian states $\rho(\mu,\Sigma)$ for classical covariances $\Sigma\succeq\tfrac12\mathbf 1$
-- statement:
--   The Gaussian states with covariance above the vacuum form a measurable family.
--
--   There is a map $\mathrm{gs}$ from pairs (mean $\mu\in\mathbb R^{2n}$, covariance $\Sigma\in\mathbb R^{2n\times2n}$) to states on the $n$-mode Fock space such that
--
--   1. $\mathrm{gs}$ is measurable for the Borel structure of the trace-norm topology on states;
--   2. every value $\mathrm{gs}(\mu,\Sigma)$ is a Gaussian state;
--   3. if $\Sigma-\tfrac12\mathbf 1$ is positive semidefinite, then $\mathrm{gs}(\mu,\Sigma)$ is the Gaussian state $\rho(\mu,\Sigma)$.
--
--   For $\Sigma\succeq\tfrac12\mathbf 1$ the state is the classical mixture of coherent states $\int|\alpha(x)\rangle\langle\alpha(x)|\,d\mathcal N(\mu,\Sigma-\tfrac12\mathbf 1)(x)$; outside this closed set $\mathrm{gs}$ is constant (the vacuum).
--
--   Role. The heterodyne tomography protocols of Theorem 8 and of [BMEM25, Theorem 10] output "a valid Gaussian state" computed measurably from the data, with a covariance that dominates the true one; under the promise $\Sigma\succeq\tfrac12\mathbf 1$ this lemma provides that output. It replaces `BosonicLearn.gaussianState_measurable_family` (which asks for all Gaussian states, including squeezed ones) in the decompositions of `BosonicLearn.theorem_8` and `BosonicLearn.bmem25_theorem_10`.
--
--   **Formalization Note** The covariance argument is a function `Fin n ⊕ Fin n → Fin n ⊕ Fin n → ℝ`, so that the domain carries the product measurable structure; `State` carries the published trace-norm topology and its Borel σ-algebra.
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, Theorem 8, p. 61 ("always outputs a valid Gaussian state"), and its proof, p. 62

import Mathlib
import Definitions.Def_BosonicLearn_IsGaussianState

open QAlgorithms.Papers.Independent.Dependency50.P33 (State traceSize)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open MeasureTheory
open scoped ENNReal Matrix

namespace BosonicLearn

/-- **A measurable family of Gaussian states with classical covariance (`Σ ⪰ ½I`).**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, Theorem 8, p. 61: the protocol "always outputs a valid Gaussian state ρ̂" computed from the heterodyne data; proof, p. 62: the
output is the Gaussian state with the estimated mean and an inflated covariance estimate, which dominates the true
covariance `Σ ⪰ (½ + ν)I ⪰ ½I`.

There is a map `gs` from pairs (mean, covariance) to states on the `n`-mode Fock space that is measurable for the
trace-norm Borel structure, takes only Gaussian states as values, and such that `gs(µ, Σ)` is the Gaussian state
`ρ(µ, Σ)` whenever `Σ − ½I` is positive semidefinite.

**Formalization Note.** For `Σ ⪰ ½I` the Gaussian state is the classical mixture of coherent states
`∫ |α(x)⟩⟨α(x)| dN(µ, Σ − ½I)(x)`, which exists and depends continuously on `(µ, Σ)`; outside this closed set `gs` may
be constant. This is the form of `gaussianState_measurable_family` needed for heterodyne tomography under the
promise `Σ ⪰ ½I`; it avoids squeezed states. The covariance argument is a function `Fin n ⊕ Fin n → Fin n ⊕ Fin n → ℝ`
so that the domain carries the product measurable structure. -/
theorem gaussianState_classical_family (n : ℕ) :
    ∃ gs : (Fin n ⊕ Fin n → ℝ) × (Fin n ⊕ Fin n → Fin n ⊕ Fin n → ℝ) → State (Occupation (Fin n)),
      Measurable gs ∧
      (∀ p, ∃ (μ : Fin n ⊕ Fin n → ℝ) (S : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ),
        IsGaussianState (gs p) μ S) ∧
      ∀ (μ : Fin n ⊕ Fin n → ℝ) (S : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ),
        (S - (1 / 2 : ℝ) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)).PosSemidef →
        IsGaussianState (gs (μ, fun a b => S a b)) μ S := by sorry

end BosonicLearn

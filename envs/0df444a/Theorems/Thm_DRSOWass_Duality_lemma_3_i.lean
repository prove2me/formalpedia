-- Prove2me | Theorems.Thm_DRSOWass_Duality_lemma_3_i
-- name    : DRSOWass.Duality.lemma_3_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T11:28:47.500869+00:00
-- url     : https://prove2.me/theorems/cffd6ba7-69d6-4f8d-aff5-f04141aac471
-- title:
--   Lemma 3(i) — Φ(λ,·), D̄(λ,·), D̲(λ,·), D̄₀(λ,·), D̲₀(λ,·) are ν-measurable
-- statement:
--   Let $(\Xi,d)$ be a Polish space, $p\in[1,\infty)$, $\nu$ a Borel probability measure and $\Psi\in L^1(\nu)$ Borel measurable. Then:
--
--   1. for every $\lambda\in\mathbb R$, $\zeta\mapsto\Phi(\lambda,\zeta)$ is $\nu$-measurable (measurable for the $\nu$-completion of the Borel $\sigma$-algebra);
--   2. for every $\lambda\ge 0$, $\overline D(\lambda,\cdot)$ and $\underline D(\lambda,\cdot)$, defined on $\{\zeta:\Phi(\lambda,\zeta)>-\infty\}$, are $\nu$-measurable;
--   3. for every $\lambda\ge 0$, $\overline D_0(\lambda,\cdot)$ and $\underline D_0(\lambda,\cdot)$, defined on $\{\zeta:\arg\min_\xi\{\lambda d^p(\xi,\zeta)-\Psi(\xi)\}\neq\emptyset\}$, are $\nu$-measurable.
--
--   The infimum defining $\Phi$ runs over uncountably many $\xi$ and $\Psi$ is not continuous, so measurability in $\zeta$ is not automatic; it is what makes the integrals in the dual problem meaningful.
--
--   **Formalization Note** A function defined only on a subset $A$ is called $\nu$-measurable when it coincides on $A$ with a $\nu$-null-measurable function on all of $\Xi$ (equivalently, it is measurable for the trace of the completed $\sigma$-algebra on $A$); this avoids any reference to the default values the total Lean functions take outside $A$. Borel measurability of $\Psi$ is added, as in the paper's p. 5.
-- source:
--   Gao, Kleywegt, Distributionally Robust Stochastic Optimization with Wasserstein Distance, arXiv:1604.02199v3, pp. 9–10, Lemma 3(i)

import Mathlib
import Definitions.Def_DRSOWass_Duality_Setting

open MeasureTheory Filter Topology

namespace DRSOWass.Duality

/-- Lemma 3(i) (Measurability), pp. 9–10: `Φ(λ, ·)` is `ν`-measurable, and `D̄(λ, ·)`,
`D̲(λ, ·)` (defined where `Φ(λ, ·) > −∞`) and `D̄₀(λ, ·)`, `D̲₀(λ, ·)` (defined where the
arg min is nonempty) are `ν`-measurable on their domains, i.e. agree there with a
`ν`-measurable function on `Ξ`. -/
theorem lemma_3_i {Ξ : Type*} [MetricSpace Ξ] [CompleteSpace Ξ] [SecondCountableTopology Ξ]
    [MeasurableSpace Ξ] [BorelSpace Ξ]
    (ν : Measure Ξ) [IsProbabilityMeasure ν] (Ψ : Ξ → ℝ) (p : ℝ)
    (hp : 1 ≤ p) (hΨm : Measurable Ψ) (hΨ : Integrable Ψ ν) :
    (∀ lam : ℝ, NullMeasurable (fun ζ => Phi Ψ p lam ζ) ν) ∧
    (∀ lam : ℝ, 0 ≤ lam → ∃ g : Ξ → ENNReal, NullMeasurable g ν ∧
      ∀ ζ, ⊥ < Phi Ψ p lam ζ → g ζ = DUpper Ψ p lam ζ) ∧
    (∀ lam : ℝ, 0 ≤ lam → ∃ g : Ξ → ENNReal, NullMeasurable g ν ∧
      ∀ ζ, ⊥ < Phi Ψ p lam ζ → g ζ = DLower Ψ p lam ζ) ∧
    (∀ lam : ℝ, 0 ≤ lam → ∃ g : Ξ → ENNReal, NullMeasurable g ν ∧
      ∀ ζ, (argminSet Ψ p lam ζ).Nonempty → g ζ = DUpper0 Ψ p lam ζ) ∧
    (∀ lam : ℝ, 0 ≤ lam → ∃ g : Ξ → ENNReal, NullMeasurable g ν ∧
      ∀ ζ, (argminSet Ψ p lam ζ).Nonempty → g ζ = DLower0 Ψ p lam ζ) := by sorry

end DRSOWass.Duality

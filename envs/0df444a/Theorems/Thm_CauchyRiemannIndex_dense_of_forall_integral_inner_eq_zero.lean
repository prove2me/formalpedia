-- Prove2me | Theorems.Thm_CauchyRiemannIndex_dense_of_forall_integral_inner_eq_zero
-- name    : CauchyRiemannIndex.dense_of_forall_integral_inner_eq_zero
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-13T23:12:43.329238+00:00
-- url     : https://prove2.me/theorems/3f550517-9d0e-45d6-afeb-83aea544cb70
-- title:
--   A subspace of $L^p(\mu;E)$ with no nonzero annihilator in $L^q(\mu;E)$ is dense ($\sigma$-finite $\mu$, finite-dimensional $E$, $1<p<\infty$)
-- statement:
--   Let $\mu$ be a $\sigma$-finite measure, $E$ a finite-dimensional real inner product space, $1<p<\infty$ and $q=p/(p-1)$ the conjugate exponent. Let $M$ be a linear subspace of $L^p(\mu;E)$ such that the only $g\in L^q(\mu;E)$ with
--   $$\int\langle v,g\rangle\,d\mu=0\quad\text{for all } v\in M$$
--   is $g=0$. Then $M$ is dense in $L^p(\mu;E)$.
--
--   This is the density criterion for subspaces of $L^p$ in terms of their annihilators in the dual exponent. It is used for statements of the form "the range of a differential operator on test functions is dense in $L^p$".
--
--   **Formalization Note.** $M$ is a `Submodule ℝ (Lp E p μ)` and the conclusion is `Dense (M : Set (Lp E p μ))`. The exponents are in `ℝ≥0∞` with `Fact (1 ≤ p)`, `Fact (1 ≤ q)`, `p.HolderConjugate q` ($p^{-1}+q^{-1}=1$), $1<p$ and $p\ne\infty$. The pairing is `∫ x, inner ℝ (v x) (g x) ∂μ` (Bochner integral; it is integrable by Hölder's inequality).
-- source:
--   H. Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations, Springer 2011, Corollary 1.8 (p. 8) and Theorem 4.11 (p. 97)

import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.ENNReal.Holder

namespace CauchyRiemannIndex

open MeasureTheory
open scoped ENNReal

/-- Let `μ` be σ-finite, `E` a finite-dimensional real inner product space, `1 < p < ∞` and `q`
the conjugate exponent. A subspace `M` of `L^p(μ; E)` is dense as soon as the only `g ∈ L^q(μ; E)`
with `∫ ⟨v, g⟩ dμ = 0` for all `v ∈ M` is `g = 0`. -/
theorem dense_of_forall_integral_inner_eq_zero {α E : Type*} [MeasurableSpace α]
    (μ : Measure α) [SigmaFinite μ] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [p.HolderConjugate q] (hp : 1 < p) (hp' : p ≠ ⊤) (M : Submodule ℝ (Lp E p μ))
    (hM : ∀ g : Lp E q μ, (∀ v ∈ M, ∫ x, inner ℝ (v x) (g x) ∂μ = 0) → g = 0) :
    Dense (M : Set (Lp E p μ)) := by
  sorry

end CauchyRiemannIndex

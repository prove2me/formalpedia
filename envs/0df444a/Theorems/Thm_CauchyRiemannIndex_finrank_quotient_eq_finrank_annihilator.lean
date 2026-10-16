-- Prove2me | Theorems.Thm_CauchyRiemannIndex_finrank_quotient_eq_finrank_annihilator
-- name    : CauchyRiemannIndex.finrank_quotient_eq_finrank_annihilator
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-16T09:39:58.468985+00:00
-- url     : https://prove2.me/theorems/f55ed0f3-3fc4-4903-a16b-b82981e714c9
-- title:
--   A closed subspace of $L^p$ with finite-dimensional annihilator in $L^q$ has finite codimension equal to that dimension
-- statement:
--   Let $\mu$ be a $\sigma$-finite measure, $E$ a finite-dimensional real inner product space, $1<p<\infty$ and $q$ the conjugate exponent, $1/p+1/q=1$. Let $M\subseteq L^p(\mu;E)$ be a closed linear subspace and let
--   $$N=\Big\{g\in L^q(\mu;E)\ :\ \int\langle v,g\rangle\,d\mu=0\ \text{for all }v\in M\Big\}$$
--   be its annihilator. If $N$ is finite-dimensional, then the quotient $L^p(\mu;E)/M$ is finite-dimensional and
--   $$\dim L^p(\mu;E)/M=\dim N.$$
--
--   This identifies the codimension of a closed subspace of $L^p$ with the dimension of its annihilator in the dual exponent. For a closed-range operator into $L^p$, it computes the dimension of the cokernel from the space of $L^q$ functions orthogonal to the range.
--
--   **Formalization Note.** $L^p(\mu;E)$ is `Lp E p μ` with `Fact (1 ≤ p)`, `1 < p`, `p ≠ ⊤`, and $q$ is given by `p.HolderConjugate q`. $N$ is passed as a submodule of `Lp E q μ` together with the hypothesis characterizing its elements as the annihilator of $M$; finite-dimensionality of $N$ is a hypothesis. The conclusion is `FiniteDimensional` of the algebraic quotient `Lp E p μ ⧸ M` together with equality of `Module.finrank`.
-- source:
--   Standard L^p duality; see e.g. H. Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations, Springer 2011, Theorem 4.11 (Riesz representation for L^p); used in C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, Lecture 4, proof of Theorem 4.20

import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.ENNReal.Holder
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

namespace CauchyRiemannIndex

open MeasureTheory
open scoped ENNReal

/-- Let `μ` be σ-finite, `E` a finite-dimensional real inner product space, `1 < p < ∞` and `q`
the conjugate exponent. Let `M` be a closed subspace of `L^p(μ; E)` and `N ⊆ L^q(μ; E)` its
annihilator `{g | ∫ ⟨v, g⟩ dμ = 0 for all v ∈ M}`. If `N` is finite-dimensional, then so is
`L^p(μ; E) / M`, and the two dimensions agree. -/
theorem finrank_quotient_eq_finrank_annihilator {α E : Type*} [MeasurableSpace α]
    (μ : Measure α) [SigmaFinite μ] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [p.HolderConjugate q] (hp : 1 < p) (hp' : p ≠ ⊤) (M : Submodule ℝ (Lp E p μ))
    (hM : IsClosed (M : Set (Lp E p μ))) (N : Submodule ℝ (Lp E q μ))
    (hN : ∀ g : Lp E q μ, g ∈ N ↔ ∀ v ∈ M, ∫ x, inner ℝ (v x) (g x) ∂μ = 0)
    (hNfin : FiniteDimensional ℝ N) :
    FiniteDimensional ℝ (Lp E p μ ⧸ M) ∧
      Module.finrank ℝ (Lp E p μ ⧸ M) = Module.finrank ℝ N := by
  sorry

end CauchyRiemannIndex

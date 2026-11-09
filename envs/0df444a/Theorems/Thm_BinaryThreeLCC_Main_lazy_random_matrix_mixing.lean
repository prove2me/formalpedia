-- Prove2me | Theorems.Thm_BinaryThreeLCC_Main_lazy_random_matrix_mixing
-- name    : BinaryThreeLCC.Main.lazy_random_matrix_mixing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T13:03:49.319968+00:00
-- url     : https://prove2.me/theorems/18462fca-073b-454b-8339-f43c6789bae0
-- title:
--   Lemma 5.7 — mixing of independent lazy stochastic matrices
-- statement:
--   Let $M$ be a measurable random real $m\times m$ matrix on any probability space, where $m\ge2$. Almost surely its entries are nonnegative, each column sums to one, and $M\ge I/2$ entrywise. Only its mean $\overline M=\mathbb E[M]$ is required to be doubly stochastic. Let the second largest eigenvalue, with multiplicity, of $(\overline M+\overline M^{\mathsf T})/2$ be at most $1-\lambda_2$, for any real $\lambda_2$ satisfying this condition. For every $r\in\mathbb N$ and every independent family $M^{(1)},\ldots,M^{(r)}$ with the law of $M$,
--
--   $$\mathbb E\left\|M^{(r)}\cdots M^{(1)}(e_u-e_{u'})\right\|_2^2
--   \le2m(1-\lambda_2)^r\qquad(u,u'\in[m]).$$
--
--   The bound for every pair is equivalent to the source's maximum bound. The empty product at $r=0$ is $I$. No finite-support restriction is imposed on the law, and sampled matrices need not have row sums one.
--
--   **Formalization Note** Matrix measurability uses the coordinate Borel sigma algebra. Stochastic entries are almost surely bounded by one; hence the entry expectations and the displayed nonnegative squared norm are integrable on the probability space. The integral's value is not supplied by a non-integrability default.
--
--   Differences from the source:
--   - encoding: finite sets with one-based indices → finite types and zero-based Fin indices; reason: a change of enumeration preserves every vertex, coordinate and edge copy
--   - encoding: independent copies of a random matrix, a maximum over u,u′, and literal second largest eigenvalue → measurable random variables on a probability space with iIndepFun and IdentDistrib, a bound for every pair, and m ≥ 2; reason: finite matrix coordinates give the same arbitrary laws, the pairwise bound is equivalent to the maximum bound, and the eigenvalue requires at least two rows
-- source:
--   Oliver Janzer, Peter Manohar, STOC 2027 submission #732 (October 2026), Lemma 5.7, printed p. 18, PDF p. 20; complete restatement; original printed pp.15–16, PDF pp.17–18; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/732.pdf

import Definitions.Def_BinaryThreeLCC_Main_RandomMatrices

set_option autoImplicit false

namespace BinaryThreeLCC.Main

/-- Lemma 5.7, for arbitrary matrix laws. Integrability follows from measurability,
probability mass one, and the almost-sure stochastic bounds; it is not assumed.
The empty product for r=0 is the identity. The gap parameter may be nonpositive. -/
theorem lazy_random_matrix_mixing {S : Type*} [MeasurableSpace S]
    (μ : MeasureTheory.Measure S) [MeasureTheory.IsProbabilityMeasure μ]
    {V : Type} [Fintype V] [DecidableEq V] (hV : 2 ≤ Fintype.card V)
    (M : S → Matrix V V ℝ) (hM : Measurable M)
    (hsample : ∀ᵐ s ∂μ, ColumnStochastic (M s) ∧ HalfLazy (M s))
    (hmean : DoublyStochastic (meanMatrix μ M))
    (gap : ℝ) (hspectral : secondLargest (symmetrized (meanMatrix μ M)) ≤ 1 - gap)
    (r : ℕ) (X : Fin r → S → Matrix V V ℝ) (hX : ∀ j, Measurable (X j))
    (hindependent : ProbabilityTheory.iIndepFun X μ)
    (hlaw : ∀ j, ProbabilityTheory.IdentDistrib (X j) M μ μ) :
    ∀ u u' : V,
      (∫ s, squaredNorm ((matrixProduct (fun j => X j s)).mulVec
        (unitVector u - unitVector u')) ∂μ) ≤
      2 * (Fintype.card V : ℝ) * (1 - gap) ^ r := by sorry

end BinaryThreeLCC.Main

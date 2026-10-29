-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_subseq_tendstoUniformly_of_intervalIntegral_sq_le
-- name    : FiniteEnergyPlane.exists_subseq_tendstoUniformly_of_intervalIntegral_sq_le
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-28T23:25:08.221919+00:00
-- url     : https://prove2.me/theorems/bdf63741-2559-4de2-80c2-4acf10940edb
-- title:
--   Periodic loops with uniformly L²-bounded values and derivatives have a uniformly convergent subsequence
-- statement:
--   Let $\iota$ be a finite index set and let $f_k:\mathbb{R}\to\mathbb{R}^\iota$ ($k\in\mathbb{N}$) be $C^1$ and $1$-periodic. Suppose there are constants $A,B$ with
--   $$\int_0^1|f_k(t)|^2\,dt\le A,\qquad \int_0^1|f_k'(t)|^2\,dt\le B\qquad\text{for all }k.$$
--   Then some subsequence $f_{\varphi(k)}$ converges uniformly on $\mathbb{R}$.
--
--   This is the compactness of $W^{1,2}$-bounded families of loops in $C^0(S^1)$. It is used to extract eigenfunctions of the asymptotic operator as limits of normalized approximate eigenfunctions (`FiniteEnergyPlane.exists_subseq_tendstoUniformly_isLoopEigen`).
--
--   **Formalization Note** $\mathbb{R}^\iota$ is `EuclideanSpace ℝ ι` with `[Fintype ι]`; differentiability is `∀ k t, HasDerivAt (f k) (f' k t) t` with each `f' k` continuous. The conclusion is `∃ φ, StrictMono φ ∧ ∃ e, TendstoUniformly (fun k => f (φ k)) e atTop`.
-- source:
--   Standard compactness for loops; used for C. Wendl, Lectures on Symplectic Field Theory, Section 4.8

import Mathlib

open MeasureTheory Filter Topology

namespace FiniteEnergyPlane

/-- A sequence of `C¹`, `1`-periodic loops `fₖ : ℝ → ℝ^ι` with `∫₀¹ ‖fₖ‖² ≤ A` and
`∫₀¹ ‖fₖ'‖² ≤ B` for all `k` has a subsequence converging uniformly on `ℝ`. -/
theorem exists_subseq_tendstoUniformly_of_intervalIntegral_sq_le
    {ι : Type*} [Fintype ι]
    (f f' : ℕ → ℝ → EuclideanSpace ℝ ι) (hf : ∀ k t, HasDerivAt (f k) (f' k t) t)
    (hf' : ∀ k, Continuous (f' k)) (hper : ∀ k, Function.Periodic (f k) 1)
    (A B : ℝ) (hA : ∀ k, ∫ t in (0:ℝ)..1, ‖f k t‖ ^ 2 ≤ A)
    (hB : ∀ k, ∫ t in (0:ℝ)..1, ‖f' k t‖ ^ 2 ≤ B) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ e : ℝ → EuclideanSpace ℝ ι,
      TendstoUniformly (fun k => f (φ k)) e atTop := by
  sorry

end FiniteEnergyPlane

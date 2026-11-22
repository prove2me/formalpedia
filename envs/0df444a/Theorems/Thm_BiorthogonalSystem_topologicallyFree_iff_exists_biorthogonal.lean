-- Prove2me | Theorems.Thm_BiorthogonalSystem_topologicallyFree_iff_exists_biorthogonal
-- name    : BiorthogonalSystem.topologicallyFree_iff_exists_biorthogonal
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T18:34:56.888519+00:00
-- url     : https://prove2.me/theorems/b2194037-9a82-4a4c-a893-7a60a4cd8431
-- title:
--   In a locally convex space a family is topologically free iff it admits biorthogonal continuous functionals
-- statement:
--   **Topologically free families and biorthogonal functionals.** Let $E$ be a complex locally convex topological vector space and $(x_i)_{i\in\iota}$ a family in $E$. The following are equivalent:
--
--   1. $(x_i)$ is *topologically free* (a minimal system): for every $i$,
--   $$x_i\notin\overline{\operatorname{span}}\{x_j: j\neq i\};$$
--   2. $(x_i)$ admits a *biorthogonal family* of continuous linear functionals: there are $u_i\in E'$ with
--   $$u_i(x_j)=\delta_{ij}\qquad(i,j\in\iota).$$
--
--   Masullo uses this criterion in the proof of Theorem 7.1.4.2(3) (p. 330), where the sequence of jet functionals $U(\delta_\rho^{(m)})$ is shown to be topologically free by producing a biorthogonal sequence, and again on p. 342 and in Chapter 4.
--
--   **Formalization Note.** Local convexity is `LocallyConvexSpace ℝ E` for the underlying real structure, with continuous addition and scalar multiplication. No Hausdorff assumption is needed for either direction. The index type is arbitrary; the paper uses countable families. The closed span is `Submodule.topologicalClosure` of `Submodule.span ℂ`.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 330, proof of Theorem 7.1.4.2(3) (also p. 342, proof of Theorem 7.3.1.2); classical reference: H. Jarchow, Locally convex spaces, Part II, Ch. 14, §14.1, Prop. 1, pp. 289–290 [Jar], as cited by the paper at these spots.

import Mathlib

open Filter Topology

set_option autoImplicit false

namespace BiorthogonalSystem

theorem topologicallyFree_iff_exists_biorthogonal
    {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℂ E] [LocallyConvexSpace ℝ E] {ι : Type*} (x : ι → E) :
    (∀ i : ι, x i ∉ (Submodule.span ℂ (x '' {j : ι | j ≠ i})).topologicalClosure) ↔
      ∃ u : ι → (E →L[ℂ] ℂ),
        (∀ i : ι, u i (x i) = 1) ∧ ∀ i j : ι, i ≠ j → u i (x j) = 0 := by sorry

end BiorthogonalSystem

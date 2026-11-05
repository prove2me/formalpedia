-- Prove2me | Theorems.Thm_FiniteEnergyPlane_isPrime_of_isFastPlane_of_isNondegenerateEnd
-- name    : FiniteEnergyPlane.isPrime_of_isFastPlane_of_isNondegenerateEnd
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-04T21:06:08.09535+00:00
-- url     : https://prove2.me/theorems/6743f03c-132b-4666-9036-518181cdf780
-- title:
--   Every asymptotic limit of a fast plane at $\infty$ is prime
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level and let $u$ be a fast finite-energy plane in the symplectization of $S$. If $u$ has a nondegenerate positive puncture at $\infty$ over a periodic Reeb orbit $P=(x,T)$, then $P$ is prime: $x(\tau)\ne x(0)$ for $0<\tau<T$.
--
--   Definition 2.14 of Hryniewicz asks only that some asymptotic limit of $u$ at $\infty$ be prime. This statement says that the property does not depend on which limit is named, so that a set of fast planes with a prescribed limit $P$ has $P$ prime as soon as it is nonempty.
--
--   **Formalization Note** `IsFastPlane H J u` and `IsNondegenerateEnd H u cylInf P 1` are the published predicates; `P.IsPrime` is the published predicate for the least positive period.
-- source:
--   U. Hryniewicz, Trans. AMS 364 (2012), arXiv:0812.4076, Section 4 (Lemma 4.17 and its proof)

import Definitions.Def_FiniteEnergyPlane_Compactness

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Let `u` be a fast finite-energy plane in the symplectization of `S ⊂ ℝ⁴` and let `P` be a periodic
Reeb orbit such that `u` has a nondegenerate positive puncture over `P` at `∞`. Then `P` is prime:
Definition 2.14 only asserts that some asymptotic limit of `u` is prime, and this says that every
asymptotic limit of `u` at `∞` is. -/
theorem isPrime_of_isFastPlane_of_isNondegenerateEnd (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V 1)
    (hfast : IsFastPlane H J u) (P : ReebOrbit H) (hnd : IsNondegenerateEnd H u cylInf P 1) :
    P.IsPrime := by
  sorry

end FiniteEnergyPlane

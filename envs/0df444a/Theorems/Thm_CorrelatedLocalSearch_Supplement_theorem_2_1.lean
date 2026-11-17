-- Prove2me | Theorems.Thm_CorrelatedLocalSearch_Supplement_theorem_2_1
-- name    : CorrelatedLocalSearch.Supplement.theorem_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T02:03:58.098313+00:00
-- url     : https://prove2.me/theorems/25c848a8-f1b7-4f73-9e76-d535ca057df8
-- title:
--   Theorem 2.1 — classical tree capacity identity
-- statement:
--   For every finite alphabet with a full-support reference law, every closed tape event $E$, $0<s\le1$ and $D\ge1$,
--   $$\max_{\nu\in\mathcal Q_{s,D}}\nu(E)=\min\{1,D C_s(E)\}.$$
--   If $E$ depends on the first $T$ symbols, a minimizing prefix-free cover exists with every word of length at most $T$. If finite-horizon events $E_T$ decrease to $N$, their worst probabilities converge to the worst probability of $N$.
--
--   Differences from the source:
--   - encoding: the displayed limit in (4) → convergence in the order topology of $\mathbb R_{\ge0}\cup\{\infty\}$; reason: this is the literal meaning of the limit
--   - encoding: probabilities and prefix capacities written as nonnegative real quantities → `ENNReal`; reason: exact extended-nonnegative encoding, including infinite capacity on an empty cover family
-- source:
--   Xu, Local Search with Correlated Randomness, arXiv:2607.17469 (sha256 17e00d69…), Theorem 2.1, p.6 (PDF p.8)

import Mathlib
import Definitions.Def_CorrelatedLocalSearch_Supplement_GeneralSource

set_option autoImplicit false

namespace CorrelatedLocalSearch.Supplement

open MeasureTheory Filter Topology
open scoped ENNReal BigOperators

/-- Xu, *Local Search with Correlated Randomness*, arXiv:2607.17469 (sha256 17e00d69…),
Theorem 2.1, p.6 (PDF p.8). Exact tree capacity identity, bounded-depth attainment, and
continuity for decreasing finite-horizon events. -/
theorem theorem_2_1 {A : Type*} [Fintype A] [MeasurableSpace A]
    [MeasurableSingletonClass A]
    [TopologicalSpace A] [DiscreteTopology A] (hA : 2 ≤ Fintype.card A)
    (pi : A -> Real) (hpi : ∀ a, 0 < pi a) (hpisum : (∑ a, pi a) = 1)
    (s D : Real) (hs0 : 0 < s) (hs1 : s ≤ 1) (hD : 1 ≤ D) (E : Set (Nat -> A))
    (hclosed : IsClosed E) :
    worstProbability pi s D E = min 1 (ENNReal.ofReal D * prefixCapacity pi s E) ∧
    (∃ nu : Measure (Nat -> A), nu ∈ SourceClass pi s D ∧
      nu E = min 1 (ENNReal.ofReal D * prefixCapacity pi s E)) ∧
    (∀ T, DependsOnFirst E T -> ∃ B : Finset (List A),
      IsPrefixFreeCover E B ∧ (∀ w ∈ B, w.length ≤ T) ∧
        coverCost pi s B = prefixCapacity pi s E) ∧
    ∀ (ET : Nat -> Set (Nat -> A)), Antitone ET ->
      (∀ T, ∃ m, DependsOnFirst (ET T) m) ->
      (⋂ T, ET T) = E ->
      Tendsto (fun T => worstProbability pi s D (ET T)) atTop
        (nhds (worstProbability pi s D E)) := by sorry

end CorrelatedLocalSearch.Supplement

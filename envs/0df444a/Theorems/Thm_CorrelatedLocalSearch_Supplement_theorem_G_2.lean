-- Prove2me | Theorems.Thm_CorrelatedLocalSearch_Supplement_theorem_G_2
-- name    : CorrelatedLocalSearch.Supplement.theorem_G_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T02:11:14.435196+00:00
-- url     : https://prove2.me/theorems/6ca83e29-23bf-4969-a874-4e1af8c35f3a
-- title:
--   Theorem G.2 — exact robustness under arbitrary interleaving
-- statement:
--   For $N\ge3$, $s=\Delta_N$ and the stated sine profile $V_N$, every deterministic nonanticipating disagreeing-edge selector on any finite union of connected components of size at least $N$ satisfies
--   $$\max_{\nu\in\mathcal Q_{s,D}}\nu\{\tau=\infty\}=\min\{1,DV_N(K_0)\}.$$
--   One source depending only on $N,K_0,D$ attains the value simultaneously for every allowed graph, initial assignment and selector. Under the independent reference source, $\mathbb E_P\tau\le25K_0/12$.
--
--   Differences from the source:
--   - encoding: disjoint union of connected graphs → a finite vertex type with a component map, symmetric within-component adjacency, explicit connectivity and component-cardinality proofs; reason: equivalent finite representation
--   - encoding: nontermination probability and expected possibly infinite running time → `ENNReal` probabilities and a lower Lebesgue integral of an infinity-valued natural count; reason: exact extended-nonnegative encoding
-- source:
--   Xu, Local Search with Correlated Randomness, arXiv:2607.17469 (sha256 17e00d69…), Theorem G.2, pp.42–43 (PDF pp.44–45)

import Mathlib
import Definitions.Def_CorrelatedLocalSearch_Supplement_SharedVoting

set_option autoImplicit false

namespace CorrelatedLocalSearch.Supplement

open MeasureTheory
open scoped ENNReal BigOperators

/-- Xu, arXiv:2607.17469 (sha256 17e00d69…), Theorem G.2, pp.42-43 (PDF pp.44-45).
For arbitrary component interleaving, the sine profile is the exact worst nontermination
probability; one source depending only on `N,K0,D` attains it for every graph, initial state and
selector simultaneously; and the independent expected work is at most `25 K0 / 12`. -/
theorem theorem_G_2 (N : Nat) (hN : 3 ≤ N) :
    (1 / 2 : Real) < votingThreshold N ∧ votingThreshold N < 1 ∧
    (∀ G : SharedVotingSystem N,
      ∀ sel : VotingSelector G, IsValidVotingSelector G sel -> ∀ D : Real, 1 ≤ D ->
        worstProbability votingPi (votingThreshold N) D
            {omega | votingTau G sel omega = ⊤} =
          ENNReal.ofReal (min 1 (D * votingValue N (initialLiveOnes G)))) ∧
    (∀ K0 : Nat, ∀ D : Real, 1 ≤ D ->
      ∃ nu : Measure (Nat -> Fin 4), nu ∈ SourceClass votingPi (votingThreshold N) D ∧
        ∀ G : SharedVotingSystem N, initialLiveOnes G = K0 ->
          ∀ sel : VotingSelector G, IsValidVotingSelector G sel ->
            nu {omega | votingTau G sel omega = ⊤} =
              ENNReal.ofReal (min 1 (D * votingValue N K0))) ∧
    ∀ G : SharedVotingSystem N,
      ∀ sel : VotingSelector G, IsValidVotingSelector G sel ->
        (∫⁻ omega, ((votingTau G sel omega : ℕ∞) : ENNReal) ∂votingReferenceMeasure) ≤
          ENNReal.ofReal ((25 / 12 : Real) * initialLiveOnes G) := by sorry

end CorrelatedLocalSearch.Supplement

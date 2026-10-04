-- Prove2me | Theorems.Thm_DermanSeqDecisions_LinProg_freq_solution_correspondence
-- name    : DermanSeqDecisions.LinProg.freq_solution_correspondence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T10:45:25.464671+00:00
-- url     : https://prove2.me/theorems/d3757d19-5919-4261-92a4-5d02bb9a388c
-- title:
--   §3, p. 21: procedures of C′ correspond to solutions of (10) via $x_{jk} = \pi_j D_{jk}$
-- statement:
--   Let $I$ be a finite state set with stochastic chance laws $q_{ij}(k)$, and suppose that for every procedure of $C'$ the states of $I$ belong to the same class. Then:
--
--   1. for every $D \in C'$ with stationary distribution $\pi$, the frequencies $x_{jk} = \pi_j D_{jk}$ solve (10),
--   $$x_{jk} \ge 0, \qquad \sum_k x_{jk} - \sum_{i \in I}\sum_k x_{ik} q_{ij}(k) = 0 \ (j \in I), \qquad \sum_{j \in I}\sum_k x_{jk} = 1,$$
--   and $\sum_k x_{jk} > 0$ for every $j$;
--   2. every solution $x$ of (10) has $\sum_k x_{jk} > 0$ for every $j \in I$; the procedure $D_{jk} = x_{jk} / \sum_k x_{jk}$ belongs to $C'$, its stationary distribution is $\pi_j = \sum_k x_{jk}$, and $x_{jk} = \pi_j D_{jk}$.
--
--   So (10) describes exactly the state-action frequencies of the procedures of $C'$, which turns optimization over $C'$ into optimization over a polytope.
--
--   **Formalization Note.** The statement is generic in $I$: the paper applies it with $I = \{0, \dots, L\}$ under Assumption A and with $I = \{-1, 0, \dots, L\}$ and the augmented law in Problem 2. "Same class" is irreducibility of the chain matrix.
-- source:
--   Derman, On Sequential Decisions and Markov Chains, Management Science 9(1):16–24 (1962), DOI 10.1287/mnsc.9.1.16, p. 21, §3, proof of Theorem 2, paragraph after (10)

import Mathlib
import Definitions.Def_JewellMRP_InfiniteStep_Model
import Definitions.Def_DermanSeqDecisions_LinProg_Model

open Matrix

namespace DermanSeqDecisions.LinProg

/-- §3, p. 21 (Derman, *On Sequential Decisions and Markov Chains*, Management Science 9(1):16–24 (1962), DOI 10.1287/mnsc.9.1.16, §3, proof of Theorem 2, the paragraph after (10), unnumbered).

Let `I` be a finite state set with stochastic chance laws `q_{ij}(k)`, and suppose that for every
procedure of `C′` the states of `I` belong to the same class. Then:
1. for every `D ∈ C′` and its stationary vector `π` (5), `x_{jk} = π_j D_{jk}` solves (10) and
   `∑_k x_{jk} > 0` for every `j ∈ I`;
2. every solution `x` of (10) has `∑_k x_{jk} > 0` for every `j ∈ I`; the procedure
   `D_{jk} = x_{jk} / ∑_k x_{jk}` belongs to `C′`, its stationary vector is `π_j = ∑_k x_{jk}`, and
   `x_{jk} = π_j D_{jk}`, so `x` is the solution of (10) that corresponds to it.

**Formalization Note.** The statement is generic in the state set `I`, as the paper uses it twice:
`I = {0, ⋯, L}` under Assumption A, and `I = {−1, 0, ⋯, L}` with the augmented law of Problem 2.
"Same class" is `Matrix.IsIrreducible` of the (row-stochastic) chain matrix. -/
theorem freq_solution_correspondence {I Act : Type*} [Fintype I] [DecidableEq I] [Fintype Act]
    (q : I → Act → I → ℝ) (hq : IsTransitionLaw q)
    (hA : ∀ D : I → Act → ℝ, IsStationaryRandomized D → (chainMatrix q D).IsIrreducible) :
    (∀ D : I → Act → ℝ, IsStationaryRandomized D → ∀ π : I → ℝ,
      JewellMRP.InfiniteStep.IsStationary (chainMatrix q D) π →
      IsFreqSolution q (fun j k => π j * D j k) ∧ ∀ j, 0 < ∑ k, π j * D j k) ∧
    ∀ x : I → Act → ℝ, IsFreqSolution q x →
      (∀ j, 0 < ∑ k, x j k) ∧ IsStationaryRandomized (decode x) ∧
      JewellMRP.InfiniteStep.IsStationary (chainMatrix q (decode x)) (fun j => ∑ k, x j k) ∧
      ∀ j k, x j k = (∑ k', x j k') * decode x j k := by sorry

end DermanSeqDecisions.LinProg

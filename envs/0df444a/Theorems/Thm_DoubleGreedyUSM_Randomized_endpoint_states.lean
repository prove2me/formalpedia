-- Prove2me | Theorems.Thm_DoubleGreedyUSM_Randomized_endpoint_states
-- name    : DoubleGreedyUSM.Randomized.endpoint_states
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T01:10:07.325+00:00
-- url     : https://prove2.me/theorems/ad3a3b57-6e1a-4372-8bc9-dddfbf126f91
-- title:
--   §III — the comparison set starts at OPT and ends at the output
-- statement:
--   Let Algorithm 2 process every element of a finite ground set exactly once, in any order. For any comparison set $OPT\subseteq\mathcal N$, the only initial state is $(X_0,Y_0)=(\varnothing,\mathcal N)$, so $OPT_0=OPT$. In every final state having nonzero probability,
--
--   $$OPT_n=X_n=Y_n.$$
--
--   These endpoint identities turn the telescoping inequality into a bound on the algorithm's returned set.
--
--   **Formalization Note** The assertion is about states of nonzero mass in the exact finite law. It is algorithmic and does not require submodularity or nonnegativity.
-- source:
--   Buchbinder, Feldman, Naor, Schwartz, A Tight Linear Time (1/2)-Approximation for Unconstrained Submodular Maximization, FOCS 2012 version, §III notation (PDF pp. 4–5)

import Mathlib
import Definitions.Def_DoubleGreedyUSM_Randomized_Algorithm2

namespace DoubleGreedyUSM.Randomized

/-- §III (PDF pp. 4–5): the initial and final comparison sets in Algorithm 2. -/
theorem endpoint_states {X : Type} [Fintype X] [DecidableEq X]
    (f : Finset X → ℝ) (l : List X) (hl : l.Nodup)
    (hcov : ∀ x : X, x ∈ l) (O : Finset X) :
    (∀ s : Finset X × Finset X,
      state f l 0 s ≠ 0 → s = (∅, Finset.univ) ∧ DoubleGreedyUSM.Deterministic.optI O s = O) ∧
    (∀ s : Finset X × Finset X,
      state f l l.length s ≠ 0 → s.1 = s.2 ∧ DoubleGreedyUSM.Deterministic.optI O s = s.1) := by sorry

end DoubleGreedyUSM.Randomized

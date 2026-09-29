-- Prove2me | Theorems.Thm_BertsekasDP_label_correcting_terminates
-- name    : BertsekasDP.label_correcting_terminates
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-06T05:11:35.112129+00:00
-- url     : https://prove2.me/theorems/efc28535-4414-45dd-819e-794f32a966b8
-- title:
--   Termination of label correcting (Prop. 2.3.1)
-- statement:
--   **Proposition 2.3.1 (termination of the label correcting method).** Consider the shortest path problem of §2.3 on a finite directed graph, and assume that every cycle has nonnegative length — formally, that every closed walk $l$ from a node $v$ back to itself satisfies
--
--   $$\ell(l) \;\ge\; 0 .$$
--
--   Then the label correcting algorithm terminates: there is **no** infinite sequence of states $\sigma_0, \sigma_1, \sigma_2, \dots$ with $\sigma_0$ the initial state and $\sigma_{k+1}$ obtained from $\sigma_k$ by one iteration of the algorithm.
--
--   Termination is the half of Prop. 2.3.1 that survives under the weaker hypothesis: it needs only that cycles do not pay, whereas the correctness half needs nonnegative arcs. The argument in the source is a counting one — each time a node enters $\mathrm{OPEN}$ its label strictly decreases to the length of some walk from the origin, and below any given bound there are only finitely many such lengths.
--
--   **Formalization Note** The claim is the negation of the existence of an infinite run starting at the initial state; it does not bound the number of iterations, and it says nothing about runs started elsewhere. Because a step requires a node in $\mathrm{OPEN}$, an infinite run would in particular keep $\mathrm{OPEN}$ nonempty forever.
-- source:
--   D. P. Bertsekas, Dynamic Programming and Optimal Control, Vol. I, 3rd ed., Athena Scientific, 2005, Proposition 2.3.1 (termination part)

import Mathlib
import Definitions.Def_BertsekasSPGraph
import Definitions.Def_BertsekasLCState

namespace BertsekasDP

theorem label_correcting_terminates {V : Type} [Fintype V] [DecidableEq V]
    (G : BertsekasSPGraph V)
    (hcyc : ∀ v l, BertsekasIsWalkFrom G v v l → 0 ≤ BertsekasWalkLength G l) :
    ¬ ∃ seq : ℕ → BertsekasLCState V,
        seq 0 = BertsekasLCInit G ∧
        ∀ k, BertsekasLCStep G (seq k) (seq (k + 1)) := by sorry

end BertsekasDP
